"""GitHub: webhook signature, which submission root a pull request touches, statuses and comments."""
from __future__ import annotations

import hashlib
import hmac
import re

import httpx

from . import contract
from .config import settings

API = "https://api.github.com"
REPO_RE = re.compile(r"^https://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+?)(?:\.git)?/?$")
SHA_RE = re.compile(r"^[0-9a-f]{7,40}$")


def verify_signature(body: bytes, signature: str | None) -> bool:
    if not settings.github_webhook_secret or not signature:
        return False
    expected = "sha256=" + hmac.new(settings.github_webhook_secret.encode(), body, hashlib.sha256).hexdigest()
    return hmac.compare_digest(expected, signature)


def _headers() -> dict:
    h = {"Accept": "application/vnd.github+json", "User-Agent": "ots.golf-verifier"}
    if settings.github_token:
        h["Authorization"] = f"Bearer {settings.github_token}"
    return h


def pr_track(owner_repo: str, number: int) -> tuple[str | None, list[str]]:
    """The track whose root the PR changes, and the files outside any root (which disqualify it)."""
    roots = {t["submission_root"].rstrip("/") + "/": t["slug"] for t in contract.tracks()}
    touched, outside = set(), []
    with httpx.Client(timeout=30) as client:
        page = 1
        while True:
            r = client.get(f"{API}/repos/{owner_repo}/pulls/{number}/files",
                           params={"per_page": 100, "page": page}, headers=_headers())
            r.raise_for_status()
            files = r.json()
            for f in files:
                name = f["filename"]
                slug = next((s for root, s in roots.items() if name.startswith(root)), None)
                if slug:
                    touched.add(slug)
                else:
                    outside.append(name)
            if len(files) < 100:
                break
            page += 1
    if len(touched) != 1:
        return None, outside
    return touched.pop(), outside


def post_status(owner_repo: str, sha: str, state: str, description: str, target_url: str) -> None:
    if not settings.github_token:
        return
    with httpx.Client(timeout=30) as client:
        client.post(f"{API}/repos/{owner_repo}/statuses/{sha}", headers=_headers(),
                    json={"state": state, "description": description[:140], "target_url": target_url,
                          "context": "ots.golf/verifier"})


def post_comment(owner_repo: str, number: int, body: str) -> None:
    if not settings.github_token:
        return
    with httpx.Client(timeout=30) as client:
        client.post(f"{API}/repos/{owner_repo}/issues/{number}/comments", headers=_headers(), json={"body": body})


FIELD_RE = re.compile(r"^\s*(assisted[ _-]?by|co[ _-]?authors?)\s*:\s*(.*?)\s*$", re.I | re.M)


def parse_pr_body(body: str) -> dict:
    """`Assisted by: ...` and `Co-authors: a, b` lines from the pull request body; the rest is the description."""
    assisted, co = None, []
    for m in FIELD_RE.finditer(body):
        key, val = m.group(1).lower().replace("-", "").replace("_", "").replace(" ", ""), m.group(2)
        if key == "assistedby":
            assisted = val or None
        else:
            co = [c.strip().lstrip("@") for c in val.split(",") if c.strip()]
    description = FIELD_RE.sub("", body).strip() or None
    return {"assisted_by": assisted, "co_authors": co, "description": description}
