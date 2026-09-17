#!/usr/bin/env python3
"""Explore conditional lower-bound attack numerics; this is NOT a Lean certificate.

    tools/tune_lower_bound.py --s-star 5309 --idx 1 --claims 24,25

For a proposed bound c, the attack assumes C_i <= c-1 for all i. Reconstruction
then costs at most v = c-1-idx and evaluates at most a = v-1 hash nodes besides
the root. For q construction attempts, T nonce trials and K target ranks, the
model estimates success as (1-delta) sum omega_l b_l and charges
B = 1024 + L*idx + T*idx + (q+2)*v + 2*idx. A contradiction would need success
(strictly) greater than B/2^127, PLUS all the mathematical attack hypotheses.

The defaults explore the bare-oracle research target, not the currently proved
claim. In particular S*=5309 is a requested exploratory value: a Bell(22) union
bound actually requires S* >= 5310 for an integer budget at epsilon=2^-9.
Counting at an integer operating point and its cost are evaluated as exact
fractions. Search, logarithms, and success use floats and the approximation
(1-x)^T ~ exp(-x*T); a positive margin is only numerical evidence. The budget
omits any new bare/separated-oracle coupling loss until that loss is proved.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import math

M, N, L = 2 ** 115, 2 ** 128, 2 ** 21
EPS = 1 / 512


def beta(a: int, d: float, s_star: int) -> float:
    rho = s_star / d
    return math.prod(((a - 1) * rho / (1 + rho) + k) / (a * rho + k)
                     for k in range(1, a + 1))


def exact_count(a: int, d: int, s_star: int) -> Fraction:
    rho = Fraction(s_star, d)
    return M * math.prod(((a - 1) * rho / (1 + rho) + k) / (a * rho + k)
                         for k in range(1, a + 1))


def bell(n: int) -> int:
    values = [1]
    for j in range(n):
        values.append(sum(math.comb(j, k) * values[k] for k in range(j + 1)))
    return values[n]


def d_min(a: int, K: int, s_star: int) -> float:
    """Threshold for M*beta_a(d) > K; compare with log2(e*q*ln(q))."""
    lo, hi = 1.0, 20000.0
    for _ in range(100):
        mid = (lo + hi) / 2
        if M * beta(a, mid, s_star) > K:
            hi = mid
        else:
            lo = mid
    return hi


def construction_threshold(q: float) -> float:
    return math.log2(math.e * q * math.log(q))


def success(a: int, K: int, T: float) -> float:
    """Estimated rank-integral success, conditional on a feasible threshold."""
    delta = math.exp(L * math.log1p(-2 ** -13))
    total = 0.0
    trial_ratio = T / N
    omega_first = -math.expm1(-trial_ratio)
    for ell in range(1, K + 1):
        omega = math.exp(-(ell - 1) * trial_ratio) * omega_first
        if ell == 1:
            b = 1.0
        else:
            z = (ell - 1) / (K * (1 - EPS))
            b = 0.0 if z >= 1 else (1 - EPS) * (
                1 - a / (a - 1) * z ** (1 / a) + z / (a - 1))
        total += omega * max(b, 0.0)
    return (1 - delta) * total


def cost(idx: int, v: int, q: float | int, T: float | int) -> float | int:
    return 1024 + L * idx + T * idx + (q + 2) * v + 2 * idx


def print_point(c: int, idx: int, s_star: int) -> None:
    """Report the previous proof's simple integer choices, with updated a and v."""
    a, v, K, d0 = c - idx - 2, c - idx - 1, 100, 123
    q, T = 5 * 2 ** 113, 3 * 2 ** 121
    count = exact_count(a, d0, s_star)
    ratio = Fraction(cost(idx, v, q, T), 2 ** 127)
    succ = success(a, K, T)
    print(f"integer point c={c}, S*={s_star}, a={a}, v={v}, K={K}, d0={d0}, "
          "q=5*2^113, T=3*2^121:")
    print(f"  exact count > K: {count > K} (count ~ {float(count):.9f}); "
          f"log2(e*q*ln(q)) ~ {construction_threshold(q):.9f}")
    print(f"  estimated success={succ:.9f}; cost/2^127={float(ratio):.9f}; "
          f"estimated margin={succ - float(ratio):+.9f}")
    print(f"  exact cost < 27/500: {ratio < Fraction(27, 500)}; "
          f"exact count > 100: {count > 100}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--idx", type=int, default=1)
    ap.add_argument("--s-star", type=int, default=5309,
                    help="exploratory information budget (default: 5309)")
    ap.add_argument("--claims", default="24,25",
                    help="proposed claims to explore, not established claims (default: 24,25)")
    ap.add_argument("--no-search", action="store_true", help="only report simple integer operating points")
    args = ap.parse_args()
    try:
        claims = list(map(int, args.claims.split(",")))
    except ValueError:
        ap.error("--claims must be comma-separated integers")
    if args.idx < 1 or args.s_star <= 0 or any(c - args.idx - 2 < 2 for c in claims):
        ap.error("require idx >= 1, s-star > 0, and c-idx-2 >= 2 for every proposed claim")
    print("CONDITIONAL NUMERICAL EXPLORATION; no proof or certificate is produced.")
    print(f"index hash = {args.idx} compression(s), S* = {args.s_star}")
    for n in (22, 23):
        value = bell(n)
        ceil_log = (value - 1).bit_length()
        print(f"Bell({n})={value}, log2 ~ {math.log2(value):.9f}, "
              f"5248+9+ceil(log2 Bell({n}))={5257 + ceil_log}")
    print("Historical labeled-model point (not a bare-oracle certificate):")
    print_point(25, 1, 5257)
    for c in claims:
        print_point(c, args.idx, args.s_star)
        if args.no_search:
            continue
        v, a = c - 1 - args.idx, c - 2 - args.idx
        best = None
        for K in (25, 50, 75, 100, 150, 200, 300, 400, 600, 800, 1200, 1600):
            need = d_min(a, K, args.s_star)
            # Success is independent of q once feasible, while cost increases in q.
            # Thus only the first feasible q in the original grid can maximize margin.
            qexp = next((x / 8 for x in range(880, 1000)
                         if construction_threshold(2 ** (x / 8)) >= need), None)
            if qexp is None:
                continue
            q = 2 ** qexp
            for Texp in (x / 8 for x in range(944, 1000)):
                T = 2 ** Texp
                s = success(a, K, T)
                r = cost(args.idx, v, q, T) / 2 ** 127
                margin = s - r
                if best is None or margin > best[0]:
                    best = (margin, K, qexp, Texp, need, s, r)
        if best is None:
            print(f"proposed c={c}: no feasible point in the search ranges")
            continue
        margin, K, qexp, Texp, d0, s, r = best
        print(f"proposed c={c} (a={a}, v={v}): best estimated margin {margin:+.7f}; "
              f"K={K}, q=2^{qexp}, T=2^{Texp}, d0 >= {d0:.6f}, "
              f"success={s:.7f}, cost/2^127={r:.7f}; "
              f"{'POSITIVE' if margin > 0 else 'NONPOSITIVE'} numerical margin")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
