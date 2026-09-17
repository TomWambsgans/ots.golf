"""ots.golf: the site, and the pull-request webhook that queues submissions."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import httpx
import markdown
import nh3
from fastapi import Depends, FastAPI, HTTPException, Request
from fastapi.concurrency import run_in_threadpool
from fastapi.responses import FileResponse, HTMLResponse, PlainTextResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from sqlalchemy import select
from sqlalchemy.orm import Session

from . import auth, charts, contract, github, records, scheme_art
from .config import settings
from .db import SessionLocal, Submission, User, get_session, init_db, utcnow

APP_DIR = Path(__file__).resolve().parent
app = FastAPI(title="ots.golf", version="0.1.0", docs_url=None, openapi_url=None, redoc_url=None)
app.mount("/static", StaticFiles(directory=APP_DIR / "static"), name="static")
templates = Jinja2Templates(directory=APP_DIR / "templates")
templates.env.filters["dt"] = lambda d: d.strftime("%Y-%m-%d %H:%M UTC") if d else ""
templates.env.filters["date"] = lambda d: d.strftime("%Y-%m-%d") if d else ""
templates.env.filters["short"] = lambda s: (s or "")[:10]
MD_TAGS = {"p", "br", "hr", "strong", "em", "del", "code", "pre", "blockquote", "ul", "ol", "li", "a",
           "h1", "h2", "h3", "h4", "h5", "h6", "table", "thead", "tbody", "tr", "th", "td"}


def safe_markdown(text: str | None) -> str:
    """Markdown written by strangers (a pull request body): rendered, then reduced to plain formatting
    tags and http(s)/mailto links. python-markdown passes raw HTML through, so this is what stands
    between a pull request and a script on the site."""
    html = markdown.markdown(text or "", extensions=["tables", "fenced_code"])
    return nh3.clean(html, tags=MD_TAGS, attributes={"a": {"href"}}, url_schemes={"http", "https", "mailto"})


templates.env.filters["md"] = safe_markdown


@app.on_event("startup")
def _startup() -> None:
    init_db()


def static_version() -> str:
    """Invalidate the stylesheet and dashboard script together when either changes."""
    assets = [APP_DIR / "static" / name for name in ("style.css", "dashboard.js")]
    return hashlib.sha256(b"".join(p.read_bytes() for p in assets if p.is_file())).hexdigest()[:10]


def render(request: Request, name: str, **ctx) -> HTMLResponse:
    ctx.update(request=request, settings=settings, contract_version=contract.load()["contract"]["version"],
               contract_id=contract.contract_id(), contract_commit=contract.trusted_commit(),
               static_v=static_version())
    ctx.setdefault("frameworks", contract.frameworks())
    ctx.setdefault("generic_upper", contract.generic_upper_candidate())
    ctx.setdefault("generic_lower", contract.generic_lower_certificate())
    ctx.setdefault("track_labels", {t["slug"]: {**t, "framework_title": contract.framework(t["framework"])["title"]}
                                    for t in contract.tracks()})
    return templates.TemplateResponse(request, name, ctx)


# --- the one way in: a pull request -----------------------------------------------------------

def queue_submission(session: Session, user: User, track: str, repo: str, commit: str, description: str | None,
                     co_authors: list[str], assisted_by: str | None, pr_number: int | None, pr_url: str | None) -> Submission:
    track_config = contract.track(track)
    if track_config is None:
        raise HTTPException(400, f"unknown track {track!r}")
    if track_config["kind"] == "upper" and track_config["framework"] != "generic":
        raise HTTPException(400, "Upper submissions require the generic algorithm framework, whose admission "
                            "proofs are still pending. DAG upper roots are retained as reference certificates.")
    commit = commit.strip().lower()
    if not github.SHA_RE.match(commit):
        raise HTTPException(400, "commit must be a hex commit hash")
    mine = [s for s in records.in_flight(session) if s.user_id == user.id]
    if len(mine) >= settings.max_inflight_per_user:
        raise HTTPException(429, f"{user.login} already has {len(mine)} submissions in flight")
    if len(records.in_flight(session)) >= settings.queue_cap:
        raise HTTPException(429, "the verification queue is full")
    dup = session.scalars(select(Submission).where(Submission.track == track, Submission.commit == commit,
                                                   Submission.source_repo == repo,
                                                   Submission.status.in_(("pending", "verifying", "verified", "rejected",
                                                                          "policy_rejected", "timeout")))).first()
    if dup:
        raise HTTPException(409, f"this commit is already submitted: {dup.id}")
    sub = Submission(track=track, user_id=user.id, source_repo=repo, commit=commit,
                     description=(description or "").strip() or None, co_authors=json.dumps(co_authors),
                     assisted_by=(assisted_by or "").strip()[:120] or None, pr_number=pr_number, pr_url=pr_url)
    session.add(sub)
    session.commit()
    return sub


MAX_WEBHOOK_BYTES = 2 * 1024 * 1024


@app.post("/webhooks/github")
async def webhook(request: Request):
    try:
        declared = int(request.headers.get("content-length") or 0)
    except ValueError:
        raise HTTPException(400, "bad content-length")
    if declared > MAX_WEBHOOK_BYTES:
        raise HTTPException(413, "payload too large")
    body = b""
    async for chunk in request.stream():
        body += chunk
        if len(body) > MAX_WEBHOOK_BYTES:
            raise HTTPException(413, "payload too large")
    if not github.verify_signature(body, request.headers.get("x-hub-signature-256")):
        raise HTTPException(401, "bad signature")
    if request.headers.get("x-github-event") != "pull_request":
        return {"ignored": True}
    try:
        ev = json.loads(body)
        action, number = ev["action"], int(ev["pull_request"]["number"])
        owner_repo, head_sha = ev["repository"]["full_name"], ev["pull_request"]["head"]["sha"]
    except (ValueError, KeyError, TypeError):
        raise HTTPException(400, "malformed event")
    if action not in ("opened", "synchronize", "reopened"):
        return {"ignored": True}
    if settings.contract_repo and owner_repo.lower() != settings.contract_repo.lower():
        return {"ignored": True, "reason": "not the contract repository"}
    return await run_in_threadpool(handle_pull_request, owner_repo, number, head_sha)   # GitHub calls block


def handle_pull_request(owner_repo: str, number: int, head_sha: str) -> dict:
    """The event only says where to look. Author, head and changed files are read from GitHub's API,
    and the head must still be the event's commit before and after the files are listed, so the
    commit that gets the verdict is the commit whose files were checked."""
    try:
        pr = github.get_pr(owner_repo, number)
        slug, outside = github.pr_track(owner_repo, number)
        pr_after = github.get_pr(owner_repo, number)
    except httpx.HTTPError as exc:
        raise HTTPException(502, f"GitHub API: {exc}")
    if pr.get("state") != "open" or pr["head"]["sha"] != head_sha or pr_after["head"]["sha"] != head_sha:
        return {"queued": False, "reason": "the pull request moved on; its newer event is the one that counts"}
    if slug is None or outside:
        github.post_comment(owner_repo, number,
                            "**ots.golf verifier:** a submission changes exactly one submission root and nothing else. "
                            + (f"Files outside a root: `{'`, `'.join(outside[:10])}`." if outside
                               else "This pull request does not change a single submission root."))
        return {"queued": False}
    head_repo = pr["head"].get("repo")
    login = (pr.get("user") or {}).get("login") or ""
    if head_repo is None or not github.LOGIN_RE.match(login):
        return {"queued": False, "reason": "the head repository is gone or the author is not a GitHub account"}
    fields = github.parse_pr_body(pr.get("body") or "")
    with SessionLocal() as session:
        submitter = auth.get_or_create_user(session, login, github_id=pr["user"]["id"],
                                            avatar_url=pr["user"].get("avatar_url"))
        try:
            sub = queue_submission(session, submitter, slug, head_repo["clone_url"], head_sha,
                                   fields["description"], fields["co_authors"], fields["assisted_by"],
                                   number, pr["html_url"])
        except HTTPException as exc:
            github.post_comment(owner_repo, number, f"**ots.golf verifier:** not queued: {exc.detail}")
            return {"queued": False, "reason": exc.detail}
    github.post_status(owner_repo, sub.commit, "pending", "queued for verification",
                       f"{settings.base_url}/submissions/{sub.id}")
    return {"queued": True, "id": sub.id}


# --- pages ------------------------------------------------------------------------------------

@app.get("/", response_class=HTMLResponse)
def home(request: Request, framework: str = "all", session: Session = Depends(get_session)):
    if framework != "all" and contract.framework(framework) is None:
        raise HTTPException(404, "unknown framework")
    models = records.overview(session)
    series = []
    for model in models:
        board = model["boards"].get("lower")
        foundation = contract.generic_lower_certificate() if model["slug"] == "generic" else None
        series.append({"slug": board["cfg"]["slug"] if board else f'{model["slug"]}-lower',
                       "framework": model["slug"], "kind": "lower", "label": f'{model["title"]} lower',
                       "baseline": board["cfg"]["baseline"] if board else foundation["claim"] if foundation else None,
                       "status": foundation["status"] if foundation else "certified",
                       "points": board["curve"] if board else []})
    upper = contract.generic_upper_candidate()
    series.append({"slug": "generic-upper", "framework": "generic", "kind": "upper",
                   "label": "Generic upper candidate", "baseline": upper["claim"],
                   "status": "candidate", "points": []})
    demo = any(b["state"]["record_demo"] for model in models for b in model["boards"].values())
    return render(request, "home.html", models=models, selected_framework=framework,
                  demo=demo, chart=charts.record_chart(series, utcnow()), art=scheme_art.svg())


@app.get("/submissions/{sub_id}", response_class=HTMLResponse)
def submission_page(sub_id: str, request: Request, session: Session = Depends(get_session)):
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    t = contract.track(sub.track)
    return render(request, "submission.html", sub=sub, t=t, framework=contract.framework(t["framework"]),
                  queue_position=next((i + 1 for i, s in enumerate(records.in_flight(session)) if s.id == sub.id), None))


@app.get("/submissions/{sub_id}/log", response_class=PlainTextResponse)
def submission_log(sub_id: str, session: Session = Depends(get_session)):
    """The verifier's transcript. Public: the submission is a public pull request anyway."""
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    if sub.log_path and Path(sub.log_path).is_file():
        return FileResponse(sub.log_path, media_type="text/plain; charset=utf-8")   # streamed, never loaded
    return "(no log yet)"


@app.get("/solvers/{login}", response_class=HTMLResponse)
def solver_page(login: str, request: Request, session: Session = Depends(get_session)):
    solver = session.scalars(select(User).where(User.login == login)).first()
    if solver is None:
        raise HTTPException(404)
    subs = list(session.scalars(select(Submission).where(Submission.user_id == solver.id)
                                .order_by(Submission.created_at.desc())))
    return render(request, "solver.html", solver=solver, subs=subs)


@app.get("/rules", response_class=HTMLResponse)
def rules(request: Request):
    return render(request, "rules.html", cfg=contract.load())


@app.get("/llms.txt", response_class=PlainTextResponse)
def llms():
    base = settings.base_url
    text = (settings.repo_root / "llms.txt").read_text(encoding="utf-8")
    return text + f"""
## Where the state is

The contract repository is the source of truth: the submission root of each track holds the
current record, and its claim.txt holds the number. Open pull requests are the submissions in
flight; the verifier's verdict is on each one as a commit status and a comment linking to
{base}/submissions/<id>, which shows status, claim, attribution and the verifier transcript.
"""
