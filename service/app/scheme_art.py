"""The concrete scheme, drawn faithfully as a radial necklace.

Root at the center; 41 hash chains of 20 beads radiating outward to their secret sources, their
ends hashed together into the root. One real signature is lit on it: one revealed value per chain,
at positions whose recomputation costs exactly 96 chain hashes (revealed values, recomputed nodes,
untouched beads), drawn uniformly from the scheme's family of disclosure sets. Every bead and edge
carries its chain and position as data attributes, so the page's script can light a fresh uniform
signature on load and every two seconds after that; the server-rendered one is only the first frame.
"""
from __future__ import annotations

import math
from functools import lru_cache

CHAINS, LEN, STEPS = 41, 20, 96
SIZE = 1100
CX = CY = SIZE / 2
R_TIP, STEP = 120, 15.5   # radius of the chain ends; beads t=20..0 from R_TIP outward


def angle(chain: int) -> float:
    return -math.pi / 2 + 2 * math.pi * chain / CHAINS


def polar(r: float, a: float) -> tuple[float, float]:
    return CX + r * math.cos(a), CY + r * math.sin(a)


def ways() -> list[list[int]]:
    """ways[k][s]: the number of ways to spend `s` chain hashes on chains k..40, each 0..20."""
    w = [[0] * (STEPS + 1) for _ in range(CHAINS + 1)]
    w[CHAINS][0] = 1
    for k in range(CHAINS - 1, -1, -1):
        for s in range(STEPS + 1):
            w[k][s] = sum(w[k + 1][s - c] for c in range(0, min(LEN, s) + 1))
    return w


def signature_positions(seed: int = 0x6f74732e676f6c66) -> list[int]:
    """Revealed positions t_k (0 = source, 20 = chain end) of one uniformly random disclosure set of
    the scheme: a uniform element of {t : sum(20 - t_k) = 96}, the family of `Cuts.lean`, sampled
    exactly by the counting table (`ways`). The seed only fixes the server-rendered first frame; the
    page's script resamples the same distribution."""
    import random
    rng = random.Random(seed)
    w = ways()
    steps, budget = [], STEPS
    for k in range(CHAINS):
        r = rng.randrange(w[k][budget])
        c = 0
        while r >= w[k + 1][budget - c]:
            r -= w[k + 1][budget - c]
            c += 1
        steps.append(c)
        budget -= c
    assert budget == 0 and sum(steps) == STEPS
    return [LEN - c for c in steps]


@lru_cache(maxsize=1)
def svg() -> str:
    pos = signature_positions()
    reach = R_TIP + LEN * STEP + 14
    out = [f'<svg viewBox="{CX - reach:.0f} {CY - reach:.0f} {2 * reach:.0f} {2 * reach:.0f}" '
           f'class="scheme-art" data-chains="{CHAINS}" data-len="{LEN}" data-steps="{STEPS}" aria-hidden="true" focusable="false">']
    edges, nodes = [], []
    for k in range(CHAINS):
        a = angle(k)
        tk = pos[k]
        pts = {t: polar(R_TIP + (LEN - t) * STEP, a) for t in range(LEN + 1)}   # t = 20 innermost

        def status(t: int) -> str:
            return "revealed" if t == tk else ("recomputed" if t > tk else "untouched")

        for t in range(1, LEN + 1):
            (x1, y1), (x2, y2) = pts[t - 1], pts[t]
            edges.append(f'<line class="e {status(t)}" data-k="{k}" data-t="{t}" x1="{x1:.1f}" y1="{y1:.1f}" '
                         f'x2="{x2:.1f}" y2="{y2:.1f}"/>')
        for t in range(LEN + 1):
            x, y = pts[t]
            if t == 0:
                s = 4.2
                nodes.append(f'<rect class="n src {status(t)}" data-k="{k}" data-t="{t}" x="{x - s:.1f}" y="{y - s:.1f}" '
                             f'width="{2 * s:.1f}" height="{2 * s:.1f}" transform="rotate(45 {x:.1f} {y:.1f})"/>')
            else:
                nodes.append(f'<circle class="n bead {status(t)}" data-k="{k}" data-t="{t}" cx="{x:.1f}" cy="{y:.1f}" r="3.4"/>')
        tx, ty = pts[LEN]
        edges.append(f'<line class="e recomputed" x1="{tx:.1f}" y1="{ty:.1f}" x2="{CX:.1f}" y2="{CY:.1f}"/>')
    nodes.append(f'<circle class="n root recomputed" cx="{CX:.1f}" cy="{CY:.1f}" r="11"/>')
    nodes.append(f'<circle class="n clasp" cx="{CX:.1f}" cy="{CY:.1f}" r="18"/>')
    out.extend(edges)
    out.extend(nodes)
    out.append("</svg>")
    return "\n".join(out)
