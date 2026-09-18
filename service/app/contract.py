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
    """Certificates explicitly linked to this class; historical classes stay separate."""
    model = framework(slug)
    if model is None:
        return {}
    return {kind: certificate for kind in ("lower", "upper")
            if f"{kind}_track" in model and (certificate := track(model[f"{kind}_track"])) is not None}


def track_framework_title(t: dict) -> str:
    """Historical certificates retain their class name when a public framework changes."""
    return t.get("historical_framework_title") or framework(t["framework"])["title"]


def generic_upper_track() -> dict | None:
    """Only the explicitly pinned generic certificate opens the public upper track."""
    certificate = framework_tracks("generic").get("upper")
    if certificate and certificate["kind"] == "upper" and certificate["framework"] == "generic":
        return certificate
    return None


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
