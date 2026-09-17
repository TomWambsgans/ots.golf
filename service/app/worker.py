"""The verifier worker: one submission at a time, through verifier/verify.py.

    .venv/bin/python -m app.worker

It picks the oldest pending submission, runs the pipeline on the trusted checkout, stores the
verdict and the log, promotes a verified submission to the record when it strictly improves the
current one, and reports back to GitHub when the submission came from a pull request.
"""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
import time
import traceback

from sqlalchemy import select

from . import contract, github, records
from .config import settings
from .db import SessionLocal, Submission, init_db, utcnow

POLL_SECONDS = 3


def _log(msg: str) -> None:
    print(f"[worker {utcnow().isoformat(timespec='seconds')}] {msg}", flush=True)


def run_pipeline(sub: Submission) -> tuple[dict, str | None]:
    """Run verify.py; return (result dict, saved log path)."""
    cfg = contract.load()
    limit = cfg["limits"]["wall_clock_seconds"]
    work = settings.data_dir / "work" / sub.id
    shutil.rmtree(work, ignore_errors=True)
    cmd = [sys.executable, str(settings.repo_root / "verifier" / "verify.py"), sub.track,
           "--source", sub.source_repo, "--commit", sub.commit, "--json", "--keep", "--work", str(work)]
    try:
        proc = subprocess.run(cmd, cwd=settings.repo_root, capture_output=True, text=True, timeout=limit + 600)
    except subprocess.TimeoutExpired:
        shutil.rmtree(work, ignore_errors=True)
        return {"status": "timeout", "reason": "pipeline exceeded its outer time limit"}, None
    log_dst = settings.data_dir / "logs" / f"{sub.id}.log"
    src_log = work / "verify.log"
    if src_log.is_file():
        shutil.copyfile(src_log, log_dst)
    else:
        log_dst.write_text(proc.stdout + "\n" + proc.stderr)
    shutil.rmtree(work, ignore_errors=True)
    try:
        out = proc.stdout
        result = json.loads(out[out.index("{"):]) if "{" in out else {}
        if not isinstance(result, dict) or "status" not in result:
            raise ValueError
    except ValueError:
        result = {"status": "failed", "reason": f"verify.py exited {proc.returncode} without a result",
                  "stderr": proc.stderr[-2000:]}
    return result, str(log_dst)


def promote(session, sub: Submission) -> None:
    """A record strictly beats every other verified claim of its track, and the contract's baseline:
    without the second condition a board whose baselines were never queued would crown anything."""
    t = contract.track(sub.track)
    order = Submission.claim.desc() if t["direction"] == "+" else Submission.claim.asc()
    best = session.scalars(select(Submission).where(Submission.track == sub.track, Submission.status == "verified",
                                                    Submission.id != sub.id, Submission.claim.is_not(None))
                           .order_by(order).limit(1)).first()
    beats_others = contract.improves(t["direction"], sub.claim, best.claim if best else None)
    beats_baseline = sub.baseline or contract.improves(t["direction"], sub.claim, t["baseline"])
    if beats_others and beats_baseline:
        sub.is_record = True
        sub.record_at = utcnow()


def report(sub: Submission) -> None:
    if not sub.pr_number or not settings.contract_repo:
        return
    url = f"{settings.base_url}/submissions/{sub.id}"
    if sub.status == "verified":
        what = f"verified: claim {sub.claim}" + (" — new record" if sub.is_record else " (not a record)")
        github.post_status(settings.contract_repo, sub.commit, "success", what, url)
        github.post_comment(settings.contract_repo, sub.pr_number,
                            f"**ots.golf verifier:** {what}. Details: {url}")
    else:
        failure = (sub.detail_dict.get("failure") or {}).get("message", "")
        what = f"{sub.status}: {failure}"[:140] if failure else sub.status
        github.post_status(settings.contract_repo, sub.commit, "failure" if sub.status != "failed" else "error", what, url)
        quoted = failure[:600].replace("```", "'''")            # compiler output is text, never markdown
        github.post_comment(settings.contract_repo, sub.pr_number,
                            f"**ots.golf verifier:** `{sub.status}`.\n\n```\n{quoted}\n```\n\nDetails: {url}")


def process(sub_id: str) -> None:
    with SessionLocal() as session:
        sub = session.get(Submission, sub_id)
        sub.status, sub.started_at = "verifying", utcnow()
        session.commit()
    _log(f"verifying {sub.id} ({sub.track}, {sub.source_repo}@{sub.commit[:10]})")
    try:
        result, log_path = run_pipeline(sub)
    except Exception:  # noqa: BLE001 - the worker must survive anything the pipeline throws
        _log(traceback.format_exc())                          # for the operator, not for the page
        result, log_path = {"status": "failed", "reason": "internal error in the verifier; the operator has the trace"}, None
    with SessionLocal() as session:
        sub = session.get(Submission, sub_id)
        sub.status = result["status"] if result["status"] in ("verified", "rejected", "policy_rejected", "timeout") else "failed"
        sub.claim = result.get("claim", sub.claim)
        sub.finished_at = utcnow()
        sub.duration_s = result.get("duration_s")
        sub.log_path = log_path
        failure = None
        if sub.status != "verified":
            msg = result.get("reason") or "; ".join(result.get("errors", [])) or result.get("tail", "")[-600:]
            failure = {"code": sub.status, "message": msg}
        sub.detail = json.dumps({"failure": failure, "commit": result.get("commit"),
                                 "comparator_exit": result.get("comparator_exit")})
        if sub.status == "verified" and sub.claim is not None:
            promote(session, sub)
        session.commit()
        _log(f"{sub.id}: {sub.status}" + (f" claim {sub.claim}" + (" RECORD" if sub.is_record else "") if sub.status == "verified" else ""))
        try:
            report(sub)
        except Exception as exc:  # noqa: BLE001
            _log(f"github report failed: {exc}")


def main() -> None:
    init_db()
    _log(f"repo {settings.repo_root}, db {settings.database_url}")
    while True:
        with SessionLocal() as session:
            # a job left in `verifying` by a crash is retried
            stale = session.scalars(select(Submission).where(Submission.status == "verifying")).all()
            for s in stale:
                s.status = "pending"
            if stale:
                session.commit()
            nxt = session.scalars(select(Submission).where(Submission.status == "pending")
                                  .order_by(Submission.created_at.asc()).limit(1)).first()
            sub_id = nxt.id if nxt else None
        if sub_id:
            process(sub_id)
        else:
            time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    main()
