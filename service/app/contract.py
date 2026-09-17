"""The contract as the service sees it: challenges.json, the pin, the trusted commit."""
from __future__ import annotations

import hashlib
import json
import subprocess
from functools import lru_cache

from .config import settings


def load() -> dict:
    return json.loads((settings.repo_root / "challenges.json").read_text(encoding="utf-8"))


def tracks() -> list[dict]:
    return load()["tracks"]


def track(slug: str) -> dict | None:
    return next((t for t in tracks() if t["slug"] == slug), None)


def frameworks() -> list[dict]:
    return load()["frameworks"]


def framework(slug: str) -> dict | None:
    return next((f for f in frameworks() if f["slug"] == slug), None)


def framework_tracks(slug: str) -> dict[str, dict]:
    """The lower/upper pair for one model; a foundation has no admitted tracks."""
    return {t["kind"]: t for t in tracks() if t["framework"] == slug}


def generic_upper_candidate() -> dict:
    """AlgorithmForest.cost is checked at 106; generic admissibility remains unproved.

    This is a reference candidate, not a record inherited from either DAG upper track.
    """
    return {"claim": 106, "status": "candidate", "framework": "generic",
            "title": "Generic algorithms", "proof": "formal/OptimalOTS/AlgorithmForest.lean"}


def generic_lower_certificate() -> dict:
    """Checked by GenericLower.candidate; the generic submission contract is still pending."""
    return {"claim": 1, "status": "foundation", "framework": "generic",
            "proof": "formal/OptimalOTS/AlgorithmLower.lean", "signing_success": "at least 1/2"}


def contract_id() -> str:
    cfg = load()
    pin = settings.repo_root / cfg["contract"]["pin_file"]
    return hashlib.sha256(pin.read_bytes()).hexdigest() if pin.is_file() else "unpinned"


@lru_cache(maxsize=1)
def trusted_commit() -> str:
    try:
        return subprocess.run(["git", "-C", str(settings.repo_root), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def improves(direction: str, claim: int, record: int | None) -> bool:
    if record is None:
        return True
    return claim > record if direction == "+" else claim < record
