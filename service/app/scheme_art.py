"""The paper's concrete scheme, drawn faithfully as a radial necklace.

Root at the center; 7 subtree digests e_l around it; 3 group digests g_j under each; 3 hash chains
of 14 beads under each group, radiating outward to their 63 secret sources. One real signature is
lit on it: a cut of cost exactly 105 with 41 revealed values (revealed values, recomputed nodes,
untouched beads), of the kind the formal proof's disclosure family contains.
"""
from __future__ import annotations

import math
from functools import lru_cache

CHAINS, LEN, PER_G, PER_E, NUM_E = 63, 14, 3, 3, 7
SIZE = 1100
CX = CY = SIZE / 2
R_E, R_G, R_TIP, STEP = 78, 140, 200, 15.5   # radii; beads t=14..0 from R_TIP outward


def angle(chain: int) -> float:
    return -math.pi / 2 + 2 * math.pi * chain / CHAINS


def polar(r: float, a: float) -> tuple[float, float]:
    return CX + r * math.cos(a), CY + r * math.sin(a)


def signature_cut() -> dict:
    """A cut of cost 105 with 41 revealed values, of the most common shape of the formal proof's
    disclosure family: two subtree digests revealed, three group digests revealed under the open
    subtrees, and one value on each of the 36 remaining chains, with chain positions of total
    cost 86 (cost 2 + 5 + 12 + 86 = 105), one of them opened all the way down to its source. The choice is pseudo-random with a fixed seed, so the
    picture is stable but does not look hand-made. Returns the status of every node."""
    import random
    rng = random.Random(0x6f74732e676f6c66)             # "ots.golf"
    revealed_e = set(rng.sample(range(NUM_E), 2))
    open_e = set(range(NUM_E)) - revealed_e
    groups_under_open = [j for l in sorted(open_e) for j in range(3 * l, 3 * l + 3)]
    revealed_g = set(rng.sample(groups_under_open, 3))
    open_g = set(groups_under_open) - revealed_g
    chains = [k for j in sorted(open_g) for k in range(3 * j, 3 * j + 3)]
    costs = {k: 0 for k in chains}                      # 14 - t_k, each at most 14, total 86
    deep, deeper = rng.sample(chains, 2)
    costs[deep], costs[deeper] = LEN, 9                 # one chain opened down to its source
    budget = 86 - LEN - 9
    while budget > 0:                                   # the rest stays shallow (at most 6 beads)
        k = rng.choice(chains)
        if k not in (deep, deeper) and costs[k] < 6:
            costs[k] += 1
            budget -= 1
    t_by_chain = {k: LEN - c for k, c in costs.items()}
    cost = 2 + sum(1 + sum(1 + sum(LEN - t_by_chain[k] for k in range(3 * j, 3 * j + 3))
                           for j in range(3 * l, 3 * l + 3) if j in open_g) for l in open_e)
    assert cost == 105, cost
    assert len(revealed_e) + len(revealed_g) + len(t_by_chain) == 41
    return {"open_e": open_e, "open_g": open_g, "revealed_e": revealed_e, "revealed_g": revealed_g,
            "t": t_by_chain}


@lru_cache(maxsize=1)
def svg() -> str:
    cut = signature_cut()
    reach = R_TIP + LEN * STEP + 14                    # outermost source plus its diamond
    out = [f'<svg viewBox="{CX - reach:.0f} {CY - reach:.0f} {2 * reach:.0f} {2 * reach:.0f}" class="scheme-art" aria-hidden="true" focusable="false">']
    edges, nodes = [], []

    def status_chain(k: int, t: int) -> str:
        if k in cut["t"]:
            tk = cut["t"][k]
            return "revealed" if t == tk else ("recomputed" if t > tk else "untouched")
        return "untouched"

    for k in range(CHAINS):
        a = angle(k)
        j, l = k // PER_G, k // (PER_G * PER_E)
        g_open = j in cut["open_g"]
        # beads t = 14 (tip, nearest the group) .. 0 (source, outermost)
        pts = {t: polar(R_TIP + (LEN - t) * STEP, a) for t in range(LEN + 1)}
        for t in range(1, LEN + 1):
            (x1, y1), (x2, y2) = pts[t - 1], pts[t]
            st = status_chain(k, t) if g_open else "untouched"
            edges.append(f'<line class="e {st}" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}"/>')
        for t in range(LEN + 1):
            x, y = pts[t]
            st = status_chain(k, t) if g_open else "untouched"
            if t == 0:
                s = 4.2
                nodes.append(f'<rect class="n src {st}" x="{x - s:.1f}" y="{y - s:.1f}" width="{2 * s:.1f}" '
                             f'height="{2 * s:.1f}" transform="rotate(45 {x:.1f} {y:.1f})"/>')
            else:
                nodes.append(f'<circle class="n bead {st}" cx="{x:.1f}" cy="{y:.1f}" r="3.4"/>')
        # tip -> group
        gx, gy = polar(R_G, angle(3 * j + 1))
        tx, ty = pts[LEN]
        st = "recomputed" if g_open else "untouched"
        edges.append(f'<line class="e {st}" x1="{tx:.1f}" y1="{ty:.1f}" x2="{gx:.1f}" y2="{gy:.1f}"/>')
    for j in range(CHAINS // PER_G):
        l = j // PER_E
        gx, gy = polar(R_G, angle(3 * j + 1))
        ex, ey = polar(R_E, angle(9 * l + 4))
        st = "revealed" if j in cut["revealed_g"] else ("recomputed" if j in cut["open_g"] else "untouched")
        est = "untouched" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e {est}" x1="{gx:.1f}" y1="{gy:.1f}" x2="{ex:.1f}" y2="{ey:.1f}"/>')
        nodes.append(f'<circle class="n g {st}" cx="{gx:.1f}" cy="{gy:.1f}" r="5.2"/>')
    for l in range(NUM_E):
        ex, ey = polar(R_E, angle(9 * l + 4))
        st = "revealed" if l in cut["revealed_e"] else "recomputed"
        edges.append(f'<line class="e recomputed" x1="{ex:.1f}" y1="{ey:.1f}" x2="{CX:.1f}" y2="{CY:.1f}"/>')
        nodes.append(f'<circle class="n e {st}" cx="{ex:.1f}" cy="{ey:.1f}" r="6.8"/>')
    nodes.append(f'<circle class="n root recomputed" cx="{CX:.1f}" cy="{CY:.1f}" r="11"/>')
    nodes.append(f'<circle class="n clasp" cx="{CX:.1f}" cy="{CY:.1f}" r="18"/>')
    out.extend(edges)
    out.extend(nodes)
    out.append("</svg>")
    return "\n".join(out)
