"""Leaderboard queries: the current record, the record frontier, the other verified submissions."""
from __future__ import annotations

from sqlalchemy import func, select
from sqlalchemy.orm import Session

from . import contract
from .db import Submission


def _verified(slug: str):
    return select(Submission).where(Submission.track == slug, Submission.status == "verified")


def current_record(session: Session, slug: str) -> Submission | None:
    t = contract.track(slug)
    order = Submission.claim.desc() if t["direction"] == "+" else Submission.claim.asc()
    return session.scalars(_verified(slug).order_by(order, Submission.finished_at.asc()).limit(1)).first()


def frontier(session: Session, slug: str) -> list[Submission]:
    return list(session.scalars(_verified(slug).where(Submission.is_record.is_(True))
                                .order_by(Submission.record_at.desc())))


def others(session: Session, slug: str) -> list[Submission]:
    return list(session.scalars(_verified(slug).where(Submission.is_record.is_(False))
                                .order_by(Submission.finished_at.desc())))


def in_flight(session: Session, slug: str | None = None) -> list[Submission]:
    q = select(Submission).where(Submission.status.in_(("pending", "verifying")))
    if slug:
        q = q.where(Submission.track == slug)
    return list(session.scalars(q.order_by(Submission.created_at.asc())))


def solver_count(session: Session, slug: str) -> int:
    return session.scalar(select(func.count(func.distinct(Submission.user_id)))
                          .where(Submission.track == slug, Submission.status == "verified")) or 0


def track_state(session: Session, t: dict) -> dict:
    rec = current_record(session, t["slug"])
    return {
        "slug": t["slug"], "title": t["title"], "direction": t["direction"], "baseline": t["baseline"],
        "record_claim": rec.claim if rec else t["baseline"],
        "record_verified": rec is not None,
        "record_submission_id": rec.id if rec else None,
        "record_setter": rec.user.login if rec else None,
        "record_at": rec.record_at.isoformat() + "Z" if rec and rec.record_at else None,
        "solvers": solver_count(session, t["slug"]),
        "in_flight": len(in_flight(session, t["slug"])),
    }


def interval(session: Session) -> dict:
    cfg = contract.load()
    lower_t = contract.track("lower")
    upper_t = contract.track("upper")
    lo = track_state(session, lower_t)
    up = track_state(session, upper_t)
    gap0 = upper_t["baseline"] - lower_t["baseline"]
    gap = up["record_claim"] - lo["record_claim"]
    progress = 1 - gap / gap0 if gap0 else 0.0
    ratio = up["record_claim"] / lo["record_claim"] if lo["record_claim"] else float("inf")
    return {"lower": lo, "upper": up, "initial_gap": gap0, "gap": gap, "progress": max(0.0, min(1.0, progress)),
            "ratio": ratio,
            "contract": {"version": cfg["contract"]["version"], "id": contract.contract_id(),
                         "commit": contract.trusted_commit()}}


def curve(session: Session, slug: str) -> list[dict]:
    """Every record of a track in the order it was set: the step curve of the record over time."""
    recs = list(session.scalars(_verified(slug).where(Submission.is_record.is_(True))
                                .order_by(Submission.record_at.asc())))
    return [{"t": s.record_at, "claim": s.claim, "id": s.id, "login": s.user.login} for s in recs]
