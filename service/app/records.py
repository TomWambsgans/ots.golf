"""Leaderboard queries: the current record, the record frontier, the in-flight submissions."""
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
    return session.scalars(_verified(slug).where(Submission.is_record.is_(True), Submission.claim.is_not(None))
                           .order_by(order, Submission.finished_at.asc()).limit(1)).first()


def frontier(session: Session, slug: str) -> list[Submission]:
    return list(session.scalars(_verified(slug).where(Submission.is_record.is_(True), Submission.claim.is_not(None))
                                .order_by(Submission.record_at.desc())))


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
        "record_demo": bool(rec and rec.detail_dict.get("demo")),
        "record_submission_id": rec.id if rec else None,
        "record_setter": rec.user.login if rec else None,
        "record_at": rec.record_at.isoformat() + "Z" if rec and rec.record_at else None,
        "solvers": solver_count(session, t["slug"]),
        "in_flight": len(in_flight(session, t["slug"])),
    }


def interval(session: Session, framework: str = "dag") -> dict:
    cfg = contract.load()
    pair = contract.framework_tracks(framework)
    return {"framework": framework,
            "lower": track_state(session, pair["lower"]) if "lower" in pair else None,
            "upper": track_state(session, pair["upper"]) if "upper" in pair else None,
            "contract": {"version": cfg["contract"]["version"], "id": contract.contract_id(),
                         "commit": contract.trusted_commit()}}


def curve(session: Session, slug: str) -> list[dict]:
    """Every record of a track in the order it was set: the step curve of the record over time."""
    recs = list(session.scalars(_verified(slug).where(Submission.is_record.is_(True), Submission.claim.is_not(None),
                                                   Submission.record_at.is_not(None))
                                .order_by(Submission.record_at.asc())))
    return [{"t": s.record_at, "claim": s.claim, "id": s.id, "login": s.user.login,
             "demo": bool(s.detail_dict.get("demo"))} for s in recs]


def overview(session: Session) -> list[dict]:
    """The three lower-bound classes; upper constructions use the generic interface only."""
    result = []
    for framework in contract.frameworks():
        boards = {}
        for kind, track in contract.framework_tracks(framework["slug"]).items():
            if kind != "lower":
                continue
            boards[kind] = board(session, track)
        result.append({**framework, "boards": boards})
    return result


def board(session: Session, track: dict) -> dict:
    return {"cfg": track, "state": track_state(session, track),
            "frontier": frontier(session, track["slug"]),
            "in_flight": in_flight(session, track["slug"]),
            "curve": curve(session, track["slug"])}
