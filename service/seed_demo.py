"""Phony leaderboard data for local development.

Adds two invented solvers (parody names, generated avatars) with verified submissions and
records over the past week, so the leaderboard, the chart and the tiles have something to show.
Everything it adds is marked with `detail = {"demo": true}` and `--remove` deletes it again. The
repository baselines and their `ots-golf` user are removed from the board (re-queue them with
`python -m app.queue <track> --baseline` when needed).

    .venv/bin/python seed_demo.py           # add (idempotent: removes its previous rows first)
    .venv/bin/python seed_demo.py --force   # the same against a database that is not the local one
    .venv/bin/python seed_demo.py --remove  # remove the phony rows only
    .venv/bin/python seed_demo.py --refresh # adapt claims and seed newly added tracks, preserving existing rows
"""
from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime, timedelta
from urllib.parse import quote

from sqlalchemy import select

from app import contract
from app.db import Base, Submission, User, engine, SessionLocal, utcnow

DEMO = {"demo": True}
NOW = utcnow().replace(microsecond=0)

# login, display name, avatar colour, initials
PEOPLE = [
    ("satoshi-nakamoto", "Satoshi Nakamoto", "#e2792e", "SN"),
    ("vitalik-buterin", "Vitalik Buterin", "#6d5ce7", "VB"),
]

# track, login, improvement over baseline, hours ago, status, is_record, assisted_by, co_authors
# (only finished rows: the worker would try to verify anything pending)
BASE_ROWS = [
    ("upper", "satoshi-nakamoto", 1, 6 * 24 + 5, "verified", True, "GPT-2", []),
    ("upper", "vitalik-buterin", 2, 4 * 24 + 11, "verified", True, "LLaMA 7B", []),
    ("upper", "satoshi-nakamoto", 3, 3 * 24 + 2, "verified", True, "GPT-2", []),
    ("upper", "vitalik-buterin", 2, 2 * 24 + 7, "verified", False, "LLaMA 7B", []),
    ("upper", "vitalik-buterin", 5, 26, "verified", True, "LLaMA 7B", []),
    ("upper", "satoshi-nakamoto", 4, 10, "verified", False, "GPT-2", []),
    ("lower", "vitalik-buterin", 1, 5 * 24 + 3, "verified", True, "LLaMA 7B", []),
    ("lower", "satoshi-nakamoto", 2, 2 * 24 + 1, "verified", True, "GPT-2", []),
    ("lower", "vitalik-buterin", 1, 22, "verified", False, "LLaMA 7B", []),
]
ROWS = BASE_ROWS + [("disclosure-" + track, *rest) for track, *rest in BASE_ROWS]


def demo_claim(track: str, improvement: int) -> int:
    cfg = contract.track(track)
    return cfg["baseline"] + (improvement if cfg["direction"] == "+" else -improvement)


def refresh(session) -> int:
    """Update demo numbers and seed missing track demos without replacing any existing row."""
    changed = 0
    existing_tracks = set()
    for sub in session.scalars(select(Submission)):
        detail = sub.detail_dict
        if detail.get("demo"):
            existing_tracks.add(sub.track)
        if detail.get("demo") and "improvement" in detail:
            claim = demo_claim(sub.track, detail["improvement"])
            if sub.claim != claim:
                sub.claim = claim
                changed += 1
    missing = {row[0] for row in ROWS} - existing_tracks
    if missing:
        changed += add_rows(session, [row for row in ROWS if row[0] in missing])
    session.commit()
    return changed


def avatar(initials: str, colour: str) -> str:
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><circle cx="32" cy="32" r="32" fill="{colour}"/>'
           f'<text x="32" y="40" font-family="Helvetica,Arial,sans-serif" font-size="26" font-weight="700" fill="#fff" '
           f'text-anchor="middle">{initials}</text></svg>')
    return "data:image/svg+xml;utf8," + quote(svg, safe="")


def remove(session) -> int:
    subs = [s for s in session.scalars(select(Submission))
            if s.detail_dict.get("demo") or (s.description or "").startswith("Demo data for local development")]
    for s in subs:
        session.delete(s)
    users = [u for u in session.scalars(select(User)) if u.github_id is None and u.login in {p[0] for p in PEOPLE}]
    for u in users:
        if not [s for s in u.submissions if s not in subs]:
            session.delete(u)
    session.commit()
    return len(subs)


def demo_users(session) -> dict:
    users = {}
    for login, name, colour, initials in PEOPLE:
        u = session.scalar(select(User).where(User.login == login))
        if u is None:
            u = User(login=login, name=name, avatar_url=avatar(initials, colour))
            session.add(u)
        users[login] = u
    session.flush()
    return users


def add_rows(session, rows) -> int:
    """Insert only the requested demo rows; leave real submissions and baselines untouched."""
    users = demo_users(session)
    for track, login, improvement, hours_ago, status, is_record, assisted, coauthors in rows:
        claim = demo_claim(track, improvement)
        t = NOW - timedelta(hours=hours_ago)
        commit = hashlib.sha1(f"{track}{login}{claim}{hours_ago}".encode()).hexdigest()
        sub = Submission(track=track, user_id=users[login].id, claim=claim if status == "verified" else None,
                         source_repo=f"https://github.com/{login}/ots.golf", commit=commit, status=status,
                         is_record=is_record, record_at=t if is_record else None, baseline=False,
                         assisted_by=assisted, co_authors=json.dumps(coauthors),
                         description="Demo data for local development; this submission does not exist.",
                         created_at=t - timedelta(minutes=4), started_at=t - timedelta(minutes=3),
                         finished_at=t if status == "verified" else None,
                         duration_s=150.0 if status == "verified" else None,
                         detail=json.dumps({**DEMO, "improvement": improvement}))
        session.add(sub)
    return len(rows)


def add(session) -> int:
    # the board is the invented solvers only: no baseline rows, no ots-golf user
    for b in session.scalars(select(Submission).where(Submission.baseline.is_(True))):
        session.delete(b)
    session.flush()
    bot = session.scalar(select(User).where(User.login == "ots-golf"))
    if bot is not None and not bot.submissions:
        session.delete(bot)

    count = add_rows(session, ROWS)
    session.commit()
    return count


def main() -> None:
    from app.config import SERVICE_DIR, settings
    local = settings.database_url == f"sqlite:///{(SERVICE_DIR / 'data').resolve() / 'ots.db'}"
    if not local and "--force" not in sys.argv:
        sys.exit(f"refusing: {settings.database_url} is not the local development database.\n"
                 "This script DELETES the verified baselines and inserts invented records; pass --force to do that anyway.")
    Base.metadata.create_all(engine)
    with SessionLocal() as session:
        if "--refresh" in sys.argv:
            print(f"updated or added {refresh(session)} demo submissions from the current baselines")
            return
        n = remove(session)
        if "--remove" in sys.argv:
            print(f"removed {n} phony submissions")
            return
        m = add(session)
        print(f"removed {n} old phony submissions, added {m}")


if __name__ == "__main__":
    main()
