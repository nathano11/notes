"""Stage A, prediction S4: the weight profile (k, l, h) at r = 1, from generalized
Bernoulli sums only (Prime_Power_Window.md, Appendix A.3).  No use of P or of the
Stickelberger engine; class numbers by reduced forms.

    B_z = - sum_{1 <= b <= m0, (b, m0) = 1} psi(b) rho_z(b) (6 b^2 - 6 m0 b + m0^2) / (24 m0),

m0 = 16 q d, psi(b) = (b/q)(b/d), rho_z(b) = z^j for b = +-5^j (mod 16).
k = v(B_1), l = v(B_-1), h = v(B_i B_-i).

Usage: python check_weight_profile.py [scan.csv] [count]
"""
import csv
import sys
from fractions import Fraction

import numpy as np

from shape_engine import class_number_forms

J16 = {1: 0, 15: 0, 5: 1, 11: 1, 9: 2, 7: 2, 13: 3, 3: 3}


def legendre_table(p):
    t = np.full(p, -1, dtype=np.int64)
    t[0] = 0
    for x in range(1, p):
        t[(x * x) % p] = 1
    return t


def v2q(x):
    x = Fraction(x)
    assert x != 0
    n, d, v = x.numerator, x.denominator, 0
    while n % 2 == 0:
        n //= 2
        v += 1
    while d % 2 == 0:
        d //= 2
        v -= 1
    return v


def values(q, d):
    m0 = 16 * q * d
    b = np.arange(1, m0, 2, dtype=np.int64)
    psi = legendre_table(q)[b % q] * legendre_table(d)[b % d]
    poly = 6 * b * b - 6 * m0 * b + m0 * m0
    cls = np.array([J16[int(x)] for x in range(1, 16, 2)], dtype=np.int64)[(b % 16) // 2]
    S = [int(np.sum((psi * poly)[cls == j])) for j in range(4)]
    den = 24 * m0
    B1 = Fraction(-(S[0] + S[1] + S[2] + S[3]), den)
    Bm1 = Fraction(-(S[0] - S[1] + S[2] - S[3]), den)
    Bi = (Fraction(-(S[0] - S[2]), den), Fraction(-(S[1] - S[3]), den))
    return B1, Bm1, Bi


def profile(q, d):
    B1, Bm1, Bi = values(q, d)
    return v2q(B1), v2q(Bm1), v2q(Bi[0] ** 2 + Bi[1] ** 2)


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "scan_5000_1e6.csv"
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    # in-sample validation against the table of A.3
    assert values(3, 7) == (-6, -54, (-66, -142)), values(3, 7)
    assert values(3, 23) == (-36, -308, (-404, -862)), values(3, 23)
    assert profile(3, 7) == (1, 1, 3) and profile(3, 23) == (2, 2, 2)
    print("in sample: (3,7) and (3,23) reproduce the table of A.3")
    with open(path) as fh:
        rows = sorted(((int(r["q"]) * int(r["d"]), int(r["q"]), int(r["d"]), int(r["leg"]))
                       for r in csv.DictReader(fh)))
    rows = rows[:count]
    tally, bad = {}, []
    for m, q, d, leg in rows:
        assert m > 5000
        k, l, h = profile(q, d)
        h4 = class_number_forms(-4 * m)
        if leg == -1:
            kind, ok = "I", (k, l, h) == (1, 1, 3)
        elif h4 % 16 == 8:
            kind, ok = "IIa", (k, l, h) == (2, 2, 2)
        else:
            assert h4 % 16 == 0
            kind, ok = "IIb", (k >= 3 and l >= 3 and h == 2)
        tally.setdefault(kind, {}).setdefault((k, l, h), 0)
        tally[kind][(k, l, h)] += 1
        if not ok:
            bad.append((q, d, leg, h4, (k, l, h)))
    print(f"S4 on the first {len(rows)} pairs of T1 (qd from {rows[0][0]} to {rows[-1][0]}):")
    for kind in sorted(tally):
        print(f"  shape {kind}: {sum(tally[kind].values())} pairs, profiles {dict(sorted(tally[kind].items()))}")
    print("  violations:", bad if bad else 0)


if __name__ == "__main__":
    main()
