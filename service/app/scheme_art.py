"""The baseline scheme, drawn faithfully as a radial necklace.

Root at the center; 7 subtree digests around it; 3 group digests under each; 3 hash chains of 14
beads under each group, radiating outward to their 63 secret sources. One real signature is lit on
it (revealed values, recomputed nodes, untouched beads), drawn uniformly from the disclosure family
of `Cuts.lean`: the cuts of reconstruction cost 105 with at most 41 revealed values, of the three
shapes (revealed subtrees, revealed groups, chain cost) = (2, 3, 86), (1, 7, 86), (2, 4, 87).
Every element carries its role and indices as data attributes, so the page's script can light a
fresh uniform signature on load and every two seconds; the server-rendered one is the first frame.
"""
from __future__ import annotations

import math
from functools import lru_cache

CHAINS, LEN, PER_G, PER_E, NUM_E = 63, 14, 3, 3, 7
SHAPES = ((2, 3, 86), (1, 7, 86), (2, 4, 87))        # (|E|, |G|, chain cost); root 2 + digests + chains = 105
SIZE = 1100
CX = CY = SIZE / 2
R_E, R_G, R_TIP, STEP = 78, 140, 200, 15.5   # radii; beads t=14..0 from R_TIP outward


def angle(chain: int) -> float:
    return -math.pi / 2 + 2 * math.pi * chain / CHAINS


def polar(r: float, a: float) -> tuple[float, float]:
    return CX + r * math.cos(a), CY + r * math.sin(a)


@lru_cache(maxsize=1)
def ways() -> list[list[int]]:
    """ways[n][s]: the number of ways to spend `s` chain hashes on `n` chains, each 0..14."""
    top = max(c for _, _, c in SHAPES)
    w = [[0] * (top + 1) for _ in range(CHAINS + 1)]
    w[0][0] = 1
    for n in range(1, CHAINS + 1):
        for s in range(top + 1):
            w[n][s] = sum(w[n - 1][s - c] for c in range(0, min(LEN, s) + 1))
    return w


def active_chains(e: int, g: int) -> int:
    return CHAINS - PER_G * PER_E * e - PER_G * g


def shape_weights() -> list[int]:
    """The number of disclosure sets of each shape: C(7, e) · C(21 - 3e, g) · ways."""
    return [math.comb(NUM_E, e) * math.comb(NUM_E * PER_E - PER_E * e, g) * ways()[active_chains(e, g)][c]
            for e, g, c in SHAPES]


def signature_cut(seed: int = 0x6f74732e676f6c66) -> dict:
    """One uniformly random disclosure set of the family, sampled exactly: the shape by its share
    of the family, the revealed digests uniformly, the chain positions through the counting table."""
    import random
    rng = random.Random(seed)
    e, g, cost = rng.choices(SHAPES, weights=shape_weights())[0]
    revealed_e = set(rng.sample(range(NUM_E), e))
    open_e = set(range(NUM_E)) - revealed_e
    groups_under_open = [j for l in sorted(open_e) for j in range(PER_E * l, PER_E * l + PER_E)]
    revealed_g = set(rng.sample(groups_under_open, g))
    open_g = set(groups_under_open) - revealed_g
    chains = [k for j in sorted(open_g) for k in range(PER_G * j, PER_G * j + PER_G)]
    w, t_by_chain, budget = ways(), {}, cost
    for i, k in enumerate(chains):
        left = len(chains) - i
        r = rng.randrange(w[left][budget])
        c = 0
        while r >= w[left - 1][budget - c]:
            r -= w[left - 1][budget - c]
            c += 1
        t_by_chain[k] = LEN - c
        budget -= c
    total = 2 + len(open_e) + len(open_g) + sum(LEN - t for t in t_by_chain.values())
    assert budget == 0 and total == 105, (budget, total)
    assert len(revealed_e) + len(revealed_g) + len(t_by_chain) <= 41
    return {"open_e": open_e, "open_g": open_g, "revealed_e": revealed_e, "revealed_g": revealed_g,
            "t": t_by_chain}


@lru_cache(maxsize=1)
def svg() -> str:
    cut = signature_cut()
    reach = R_TIP + LEN * STEP + 14                    # outermost source plus its diamond
    shapes = ";".join(f"{e},{g},{c}" for e, g, c in SHAPES)
    out = [f'<svg viewBox="{CX - reach:.0f} {CY - reach:.0f} {2 * reach:.0f} {2 * reach:.0f}" class="scheme-art" '
           f'data-len="{LEN}" data-shapes="{shapes}" aria-hidden="true" focusable="false">']
    edges, nodes = [], []

    def status_chain(k: int, t: int) -> str:
        if k in cut["t"]:
            tk = cut["t"][k]
            return "revealed" if t == tk else ("recomputed" if t > tk else "untouched")
        return "untouched"

    for k in range(CHAINS):
        a = angle(k)
        j = k // PER_G
        g_open = j in cut["open_g"]
        # beads t = 14 (tip, nearest the group) .. 0 (source, outermost)
        pts = {t: polar(R_TIP + (LEN - t) * STEP, a) for t in range(LEN + 1)}
        for t in range(1, LEN + 1):
            (x1, y1), (x2, y2) = pts[t - 1], pts[t]
            st = "recomputed" if status_chain(k, t) == "recomputed" else "untouched"
            edges.append(f'<line class="e {st}" data-r="cedge" data-k="{k}" data-t="{t}" x1="{x1:.1f}" y1="{y1:.1f}" '
                         f'x2="{x2:.1f}" y2="{y2:.1f}"/>')
        for t in range(LEN + 1):
            x, y = pts[t]
            st = status_chain(k, t)
            if t == 0:
                s = 5.2
                nodes.append(f'<rect class="n src {st}" data-r="bead" data-k="{k}" data-t="{t}" x="{x - s:.1f}" '
                             f'y="{y - s:.1f}" width="{2 * s:.1f}" height="{2 * s:.1f}" '
                             f'transform="rotate(45 {x:.1f} {y:.1f})"/>')
            else:
                nodes.append(f'<circle class="n bead {st}" data-r="bead" data-k="{k}" data-t="{t}" cx="{x:.1f}" '
                             f'cy="{y:.1f}" r="4.3"/>')
        # tip -> group
        gx, gy = polar(R_G, angle(PER_G * j + 1))
        tx, ty = pts[LEN]
        st = "recomputed" if g_open else "untouched"
        edges.append(f'<line class="e {st}" data-r="tip" data-g="{j}" x1="{tx:.1f}" y1="{ty:.1f}" x2="{gx:.1f}" y2="{gy:.1f}"/>')
    for j in range(CHAINS // PER_G):
        l = j // PER_E
        gx, gy = polar(R_G, angle(PER_G * j + 1))
        ex, ey = polar(R_E, angle(PER_G * PER_E * l + 4))
        st = "revealed" if j in cut["revealed_g"] else ("recomputed" if j in cut["open_g"] else "untouched")
        est = "untouched" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e {est}" data-r="gedge" data-s="{l}" x1="{gx:.1f}" y1="{gy:.1f}" x2="{ex:.1f}" y2="{ey:.1f}"/>')
        nodes.append(f'<circle class="n g {st}" data-r="g" data-g="{j}" cx="{gx:.1f}" cy="{gy:.1f}" r="6.5"/>')
    for l in range(NUM_E):
        ex, ey = polar(R_E, angle(PER_G * PER_E * l + 4))
        st = "revealed" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e recomputed" x1="{ex:.1f}" y1="{ey:.1f}" x2="{CX:.1f}" y2="{CY:.1f}"/>')
        nodes.append(f'<circle class="n e {st}" data-r="s" data-s="{l}" cx="{ex:.1f}" cy="{ey:.1f}" r="8.5"/>')
    nodes.append(f'<circle class="n root recomputed" cx="{CX:.1f}" cy="{CY:.1f}" r="13.5"/>')
    nodes.append(f'<circle class="n clasp" cx="{CX:.1f}" cy="{CY:.1f}" r="21"/>')
    out.extend(edges)
    out.extend(nodes)
    out.append("</svg>")
    return "\n".join(out)
