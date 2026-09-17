#!/usr/bin/env python3
"""Render a track's challenge stub from its template with the submission's claim.

    render_challenge.py TRACK [--claim N] [--root DIR]

The claim defaults to the track's `<submission_root>/claim.txt`. The rendered file is what
comparator compares the submission against, so the number in the kernel-checked statement is
exactly the number the leaderboard reads.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from contract import ContractError, load_challenges, read_claim, repo_root, track  # noqa: E402


def render(root: Path, slug: str, claim: int | None) -> tuple[Path, int]:
    cfg = load_challenges(root)
    t = track(cfg, slug)
    if claim is None:
        claim = read_claim(root / t["submission_root"] / "claim.txt", cfg["limits"]["max_claim"])
    if not 0 <= claim <= cfg["limits"]["max_claim"]:
        raise ContractError(f"claim must be between 0 and {cfg['limits']['max_claim']}")
    template = (root / t["challenge_template"]).read_text(encoding="utf-8")
    if "{{CLAIM}}" not in template:
        raise ContractError(f"{t['challenge_template']} has no {{{{CLAIM}}}} placeholder")
    out = root / t["challenge_file"]
    out.write_text(template.replace("{{CLAIM}}", str(claim)), encoding="utf-8")
    return out, claim


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("track")
    ap.add_argument("--claim", type=int)
    ap.add_argument("--root", type=Path)
    a = ap.parse_args()
    try:
        out, claim = render(a.root or repo_root(), a.track, a.claim)
    except ContractError as exc:
        print(f"render_challenge: {exc}", file=sys.stderr)
        return 1
    print(f"{out} (claim {claim})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
