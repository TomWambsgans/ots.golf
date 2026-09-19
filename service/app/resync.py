"""Rebuild the database from GitHub, so the server holds nothing that cannot be recreated.

    .venv/bin/python -m app.resync

GitHub keeps everything durable: pull requests (author, description, attribution, head commits,
merges), each head's code and NOTES.md under refs/pull/<N>/head, and every verdict in the hidden
block of the verifier's own comment. A rebuild reads them back, recomputes records from the merges
in merge order, and queues any open head that has no verdict yet. It only adds what is missing,
so running it on a live database is harmless.
"""
from __future__ import annotations

import json
from datetime import datetime

from sqlalchemy import select

from . import auth, contract, github
from .config import settings
from .db import SessionLocal, Submission, init_db, local_lock, pr_submission_id, stable_id, utcnow

FINISHED = {"verified", "rejected", "policy_rejected", "timeout", "failed"}


def _time(value) -> datetime | None:
    if not isinstance(value, str):
        return None
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError:
        return None


def resync(queue_open_heads: bool = True) -> dict:
    """Restore every pull request's checked heads. Returns counts for the log."""
    if not settings.github_token or not settings.submissions_repo:
        return {"skipped": "no GitHub token or submissions repository configured"}
    repo = settings.submissions_repo
    bot = (settings.bot_login or github.token_login()).lower()
    restored, queued, merged = 0, [], []
    for pr in github.list_pulls(repo):
        number, head = pr["number"], pr["head"]["sha"]
        pr_url = f"https://github.com/{repo}/pull/{number}"
        author = pr.get("user") or {}
        if not github.LOGIN_RE.fullmatch(author.get("login") or ""):
            continue
        verdicts, comment_id = [], None
        for c in github.list_comments(repo, number):
            if ((c.get("user") or {}).get("login") or "").lower() == bot:
                found = github.parse_verdicts(c.get("body") or "")
                if found:
                    verdicts, comment_id = found, c.get("id")
        fields = github.parse_pr_body(pr.get("body") or "")
        head_repo = (pr["head"].get("repo") or {}).get("clone_url") or f"https://github.com/{repo}.git"
        merge = ({"head": head, "repository": repo, "number": number, "merged_at": pr.get("merged_at")}
                 if pr.get("merged_at") else None)
        with local_lock("results"), SessionLocal() as session:
            user = auth.get_or_create_user(session, author["login"], github_id=author.get("id"),
                                           avatar_url=author.get("avatar_url"))
            for v in verdicts:
                t = contract.track(v["track"])
                if t is None or v["status"] not in FINISHED:
                    continue
                sid = pr_submission_id(repo, number, v["commit"])
                if session.get(Submission, sid) is not None:
                    continue
                detail = {"contract": v.get("contract"), "restored": True}
                if type(comment_id) is int:
                    detail["github_comment_id"] = comment_id
                if merge and merge["head"] == v["commit"]:
                    detail["merge"] = merge
                notes = github.read_file(repo, f'{t["submission_root"]}/NOTES.md', v["commit"])
                if notes and notes.strip():
                    detail["notes"] = notes.strip()
                finished = _time(v.get("finished_at"))
                session.add(Submission(
                    id=sid, track=v["track"], user_id=user.id, source_repo=head_repo, commit=v["commit"],
                    claim=v.get("claim"), status=v["status"], description=fields["description"],
                    co_authors=json.dumps(fields["co_authors"]), assisted_by=fields["assisted_by"],
                    pr_number=number, pr_url=pr_url, created_at=finished or _time(pr.get("created_at")),
                    finished_at=finished, duration_s=v.get("duration_s"), detail=json.dumps(detail)))
                restored += 1
            session.commit()
        if merge:
            merged.append((merge["merged_at"], pr_url, head))
        if queue_open_heads and pr.get("state") == "open" and head not in {v["commit"] for v in verdicts}:
            queued.append((repo, number, head))
    promoted = _promote_merged(merged)
    if queued:
        from .main import handle_pull_request
        for repo_, number, head in queued:
            handle_pull_request(repo_, number, head)
    return {"restored": restored, "promoted": promoted, "queued": len(queued)}


def _promote_merged(merged: list[tuple]) -> int:
    """Replay the merges in merge order, so each record is decided as it was at the time."""
    from .worker import promote
    count = 0
    with local_lock("results"), SessionLocal() as session:
        for merged_at, pr_url, head in sorted(merged):
            sub = session.scalars(select(Submission).where(Submission.pr_url == pr_url,
                                                           Submission.commit == head)).first()
            if sub is None or sub.status != "verified" or sub.is_record:
                continue
            promote(session, sub, at=_time(merged_at))
            session.flush()
            count += sub.is_record
        session.commit()
    return count


def public_tracks() -> list[dict]:
    cfg = contract.load()
    public = {f["lower_track"] for f in cfg["frameworks"] if "lower_track" in f} | set(cfg["upper_tracks"])
    return [t for t in contract.tracks() if t["slug"] in public]


def ensure_baselines() -> int:
    """Each public track starts from its reference certificate, pinned in the contract repository at
    the claim in challenges.json. Recreate the missing baseline rows; they need no GitHub state."""
    from .worker import promote
    added = 0
    commit = contract.trusted_commit()
    with local_lock("results"), SessionLocal() as session:
        for t in public_tracks():
            if session.scalars(select(Submission).where(Submission.track == t["slug"],
                                                        Submission.baseline.is_(True))).first():
                continue
            user = auth.get_or_create_user(session, "ots.golf", name="ots.golf (baseline)")
            sub = Submission(
                id=stable_id("baseline", t["slug"], commit), track=t["slug"], user_id=user.id,
                source_repo=f"https://github.com/{settings.contract_repo}.git", commit=commit,
                claim=t["baseline"], status="verified", baseline=True, finished_at=utcnow(),
                description=f"Reference certificate of the {t['title'].lower()} track, shipped in the contract repository.",
                detail=json.dumps({"reference": True, "contract": contract.contract_id()}))
            session.add(sub)
            session.flush()
            promote(session, sub)
            added += 1
        session.commit()
    return added


def main() -> int:
    init_db()
    print(json.dumps(resync(), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
