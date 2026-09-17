#!/usr/bin/env python3
"""Numeric model of the lower-bound attack (paper Sections 5-6, Appendix B), to re-tune its
operating point under a cost model where the index hash costs `idx` compressions.

    tools/tune_lower_bound.py [--idx 2] [--claims 25,24,23]

For a claimed bound c (every secure scheme has some C_i >= c), the attack assumes C_i <= c-1 for
all i, so reconstruction costs at most v = c-1-idx and evaluates at most a = v-1 hash nodes besides
the root. The attack with q construction attempts, T nonce trials and K target ranks succeeds with
probability (1-δ)·Σ ω_ℓ b_ℓ and costs B = 1024 + L·idx + T·idx + (q+2)·v + 2·idx; the contradiction
needs success > B / 2^127.
"""
from __future__ import annotations

import argparse
import math

S_STAR, M, N, L = 5257, 2 ** 115, 2 ** 128, 2 ** 21
EPS = 1 / 512


def beta(a: int, d: float) -> float:
    rho = S_STAR / d
    return math.prod(((a - 1) * rho / (1 + rho) + k) / (a * rho + k) for k in range(1, a + 1))


def d_min(a: int, K: int) -> float:
    """Smallest d with M·β_a(d) > K (β_a increases with d). The threshold d0 must be at least this
    (counting bound) and at most log2(e q ln q) (construction bound)."""
    lo, hi = 1.0, 20000.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if M * beta(a, mid) > K:
            hi = mid
        else:
            lo = mid
    return hi


def construction_threshold(q: float) -> float:
    return math.log2(math.e * q * math.log(q))


def success(a: int, K: int, q: float, T: float, d0: float) -> float:
    """(1-δ) Σ_ℓ ω_ℓ b_ℓ with b_ℓ from the integral of the rank bound, threshold d0 = min(d0, log(e q ln q))."""
    delta = (1 - 2 ** -13) ** L
    total = 0.0
    for ell in range(1, K + 1):
        omega = math.exp(-(ell - 1) * T / N) - math.exp(-ell * T / N)   # (1-x)^T ≈ e^{-xT}, tiny x
        if ell == 1:
            b = 1.0
        else:
            z = (ell - 1) / (K * (1 - EPS))          # = 512(ℓ-1)/(511 K)
            if z >= 1:
                b = 0.0
            else:
                b = (1 - EPS) * (1 - a / (a - 1) * z ** (1 / a) + z / (a - 1))
        total += omega * max(b, 0.0)
    return (1 - delta) * total


def cost(idx: int, v: int, q: float, T: float) -> float:
    return 1024 + L * idx + T * idx + (q + 2) * v + 2 * idx


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--idx", type=int, default=2)
    ap.add_argument("--claims", default="25,24,23")
    a_ = ap.parse_args()
    print(f"index hash = {a_.idx} compression(s)")
    # sanity: the point of the earlier cost model, without overhead bits (idx 1, c = 25: a = 22, v = 23, K = 100, q = 5·2^113, T = 3·2^121)
    q0, T0 = 5 * 2 ** 113, 3 * 2 ** 121
    print(f"earlier point (idx 1): d_min(22,100) = {d_min(22, 100):.2f} <= log(e q ln q) = {construction_threshold(q0):.2f} "
          f"(then: d0 = 123); success = {success(22, 100, q0, T0, 123):.5f} (then > 0.055); "
          f"cost/2^127 = {cost(1, 23, q0, T0) / 2 ** 127:.5f} (then < 0.054)")
    for c in map(int, a_.claims.split(",")):
        v = c - 1 - a_.idx
        a = v - 1
        best = None
        for K in (25, 50, 75, 100, 150, 200, 300, 400, 600, 800, 1200, 1600):
            need = d_min(a, K)
            for qexp in [x / 8 for x in range(880, 1000)]:      # q = 2^qexp
                q = 2 ** qexp
                if construction_threshold(q) < need:
                    continue                                    # counting and construction thresholds incompatible
                for Texp in [x / 8 for x in range(944, 1000)]:  # T = 2^Texp
                    T = 2 ** Texp
                    s = success(a, K, q, T, need)
                    r = cost(a_.idx, v, q, T) / 2 ** 127
                    margin = s - r
                    if best is None or margin > best[0]:
                        best = (margin, K, qexp, Texp, need, s, r)
        if best is None:
            print(f"claim c = {c}: no feasible point in the search ranges")
            continue
        margin, K, qexp, Texp, d0, s, r = best
        print(f"claim c = {c} (a = {a}, v = {v}): best margin {margin:+.4f}  K = {K}, q = 2^{qexp}, T = 2^{Texp}, "
              f"d0 >= {d0:.1f}, success = {s:.4f}, cost/2^127 = {r:.4f}  -> {'FEASIBLE' if margin > 0 else 'infeasible'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
