"""ots.golf: the site, and the pull-request webhook that queues submissions."""
from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path

import markdown
from fastapi import Depends, FastAPI, HTTPException, Request
from fastapi.responses import HTMLResponse, PlainTextResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from sqlalchemy import select
from sqlalchemy.orm import Session

from . import auth, charts, contract, github, records
from .config import settings
from .db import Submission, User, get_session, init_db, utcnow

APP_DIR = Path(__file__).resolve().parent
app = FastAPI(title="ots.golf", version="0.1.0", docs_url=None, openapi_url=None, redoc_url=None)
app.mount("/static", StaticFiles(directory=APP_DIR / "static"), name="static")
templates = Jinja2Templates(directory=APP_DIR / "templates")
templates.env.filters["dt"] = lambda d: d.strftime("%Y-%m-%d %H:%M UTC") if d else ""
templates.env.filters["date"] = lambda d: d.strftime("%Y-%m-%d") if d else ""
templates.env.filters["short"] = lambda s: (s or "")[:10]
templates.env.filters["md"] = lambda s: markdown.markdown(s or "", extensions=["tables", "fenced_code"])


@app.on_event("startup")
def _startup() -> None:
    init_db()


def render(request: Request, name: str, **ctx) -> HTMLResponse:
    ctx.update(request=request, settings=settings, contract_version=contract.load()["contract"]["version"],
               contract_id=contract.contract_id(), contract_commit=contract.trusted_commit())
    return templates.TemplateResponse(request, name, ctx)


# --- the one way in: a pull request -----------------------------------------------------------

def queue_submission(session: Session, user: User, track: str, repo: str, commit: str, description: str | None,
                     co_authors: list[str], assisted_by: str | None, pr_number: int | None, pr_url: str | None) -> Submission:
    if contract.track(track) is None:
        raise HTTPException(400, f"unknown track {track!r}")
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
                                                   Submission.status.in_(("pending", "verifying", "verified")))).first()
    if dup:
        raise HTTPException(409, f"this commit is already submitted: {dup.id}")
    sub = Submission(track=track, user_id=user.id, source_repo=repo, commit=commit,
                     description=(description or "").strip() or None, co_authors=json.dumps(co_authors),
                     assisted_by=(assisted_by or "").strip()[:120] or None, pr_number=pr_number, pr_url=pr_url)
    session.add(sub)
    session.commit()
    return sub


@app.post("/webhooks/github")
async def webhook(request: Request, session: Session = Depends(get_session)):
    body = await request.body()
    if not github.verify_signature(body, request.headers.get("x-hub-signature-256")):
        raise HTTPException(401, "bad signature")
    if request.headers.get("x-github-event") != "pull_request":
        return {"ignored": True}
    ev = json.loads(body)
    if ev.get("action") not in ("opened", "synchronize", "reopened"):
        return {"ignored": True}
    pr = ev["pull_request"]
    owner_repo = ev["repository"]["full_name"]
    slug, outside = github.pr_track(owner_repo, pr["number"])
    if slug is None or outside:
        github.post_comment(owner_repo, pr["number"],
                            "**ots.golf verifier:** a submission changes exactly one submission root and nothing else. "
                            + (f"Files outside a root: `{'`, `'.join(outside[:10])}`." if outside
                               else "This pull request does not change a single submission root."))
        return {"queued": False}
    fields = github.parse_pr_body(pr.get("body") or "")
    submitter = auth.get_or_create_user(session, pr["user"]["login"], github_id=pr["user"]["id"],
                                        avatar_url=pr["user"].get("avatar_url"))
    try:
        sub = queue_submission(session, submitter, slug, pr["head"]["repo"]["clone_url"], pr["head"]["sha"],
                               fields["description"], fields["co_authors"], fields["assisted_by"],
                               pr["number"], pr["html_url"])
    except HTTPException as exc:
        github.post_comment(owner_repo, pr["number"], f"**ots.golf verifier:** not queued: {exc.detail}")
        return {"queued": False, "reason": exc.detail}
    github.post_status(owner_repo, sub.commit, "pending", "queued for verification",
                       f"{settings.base_url}/submissions/{sub.id}")
    return {"queued": True, "id": sub.id}


# --- pages ------------------------------------------------------------------------------------

@app.get("/", response_class=HTMLResponse)
def home(request: Request, session: Session = Depends(get_session)):
    iv = records.interval(session)
    boards = {t["slug"]: {"cfg": t, "frontier": records.frontier(session, t["slug"])[:10],
                          "others": records.others(session, t["slug"])[:5],
                          "in_flight": records.in_flight(session, t["slug"])} for t in contract.tracks()}
    literature = load_literature()
    chart = charts.record_chart({t["slug"]: records.curve(session, t["slug"]) for t in contract.tracks()},
                                {t["slug"]: t["baseline"] for t in contract.tracks()}, utcnow(), literature)
    return render(request, "home.html", interval=iv, boards=boards, chart=chart, literature=literature)


def load_literature() -> list[dict]:
    p = settings.repo_root / "docs" / "literature.json"
    if not p.is_file():
        return []
    pts = json.loads(p.read_text(encoding="utf-8")).get("points", [])
    for pt in pts:
        pt["t"] = datetime.strptime(pt["date"], "%Y-%m-%d")
    return pts


@app.get("/tracks/{slug}", response_class=HTMLResponse)
def track_page(slug: str, request: Request, session: Session = Depends(get_session)):
    t = contract.track(slug)
    if t is None:
        raise HTTPException(404)
    return render(request, "track.html", t=t, state=records.track_state(session, t),
                  frontier=records.frontier(session, slug), others=records.others(session, slug),
                  in_flight=records.in_flight(session, slug))


@app.get("/submissions/{sub_id}", response_class=HTMLResponse)
def submission_page(sub_id: str, request: Request, session: Session = Depends(get_session)):
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    return render(request, "submission.html", sub=sub, t=contract.track(sub.track),
                  queue_position=next((i + 1 for i, s in enumerate(records.in_flight(session)) if s.id == sub.id), None))


@app.get("/submissions/{sub_id}/log", response_class=PlainTextResponse)
def submission_log(sub_id: str, session: Session = Depends(get_session)):
    """The verifier's transcript. Public: the submission is a public pull request anyway."""
    sub = session.get(Submission, sub_id)
    if sub is None:
        raise HTTPException(404)
    if sub.log_path and Path(sub.log_path).is_file():
        return Path(sub.log_path).read_text(errors="replace")
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
    text = (settings.repo_root / "AGENTS.md").read_text(encoding="utf-8")
    return render(request, "rules.html", body=markdown.markdown(text, extensions=["tables", "fenced_code"]),
                  cfg=contract.load())


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
