"""Shared helpers for the ots.golf verifier scripts. Standard library only."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

CLAIM_RE = re.compile(r"^(0|[1-9][0-9]*)\n?$")
LEAN_FILE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*\.lean$")


class ContractError(Exception):
    pass


def repo_root(start: Path | None = None) -> Path:
    p = (start or Path(__file__).resolve().parent).resolve()
    for cand in (p, *p.parents):
        if (cand / "challenges.json").is_file():
            return cand
    raise ContractError("challenges.json not found above %s" % p)


def load_challenges(root: Path) -> dict:
    try:
        return json.loads((root / "challenges.json").read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ContractError(f"cannot read challenges.json: {exc}") from exc


def track(cfg: dict, slug: str) -> dict:
    for t in cfg["tracks"]:
        if t["slug"] == slug:
            return t
    raise ContractError(f"unknown track {slug!r}; known: {[t['slug'] for t in cfg['tracks']]}")


def read_claim(path: Path, max_claim: int) -> int:
    """The claim file holds one canonical non-negative integer and at most one trailing newline."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ContractError(f"cannot read {path}: {exc}") from exc
    if not CLAIM_RE.match(text):
        raise ContractError(f"{path}: expected a canonical integer followed by at most one newline")
    value = int(text.strip())
    if value > max_claim:
        raise ContractError(f"{path}: claim {value} exceeds max_claim {max_claim}")
    return value


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def improves(direction: str, claim: int, record: int) -> bool:
    return claim > record if direction == "+" else claim < record
