"""Executable check of every residue symbol used in the two Redei matrices.

For each pair (q, d) in a scan file: write d = x^2 - 2 y^2 (x, y > 0 odd),
pi = x + y sqrt2, pi' = x - y sqrt2, eps = 1 + sqrt2, beta = 2 + sqrt2,
pi* = (-1/y) eps pi.  Entries are computed from their definitions
(Legendre symbols in the residue fields, the 2-adic square class of pi*),
not from the closed forms proved in Dyadic_Residue_Shape.md; the closed
forms and the two F_2-ranks are then asserted.

Usage: python check_redei_symbols.py SCAN.csv [SCAN2.csv ...]
"""
import csv
import sys
from math import isqrt


def leg(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def rank_f2(rows):
    rows = [r[:] for r in rows]
    rk = 0
    for col in range(3):
        piv = next((i for i in range(rk, 3) if rows[i][col]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(3):
            if i != rk and rows[i][col]:
                rows[i] = [(a + b) % 2 for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def bit(sym: int) -> int:
    assert sym in (1, -1)
    return 0 if sym == 1 else 1


def check(q: int, d: int):
    y = 1
    while True:
        x2 = d + 2 * y * y
        x = isqrt(x2)
        if x * x == x2:
            break
        y += 2
    assert x % 2 == 1 and x * x - 2 * y * y == d
    sig = 1 if y % 4 == 1 else -1
    A, B = sig * (x + 2 * y), sig * (x + y)                # pi* = A + B sqrt2
    assert A * A - 2 * B * B == -d
    assert (A % 4, B % 4) in ((1, 0), (3, 2))              # pi* is a square mod 4
    u = 0 if (A % 8, B % 4) in ((1, 0), (3, 2)) else 1     # non-square in Q_2(sqrt2)
    r = x * pow(y, -1, d) % d                              # sqrt2 mod pi' ; -r mod pi
    s = leg(A + B * r, d)                                  # (pi*/pi')
    assert s == leg(A - B * (-r), d)                       # (pi'*/pi), conjugate symbol
    beta_pi, beta_pi2 = leg(2 - r, d), leg(2 + r, d)       # (beta/pi), (beta/pi')
    c = bit(leg(q, d))
    # closed forms proved in the manuscript
    assert x % 8 in (3, 5)                                 # d = 7 (16)
    assert s == -1 and u == 1 and beta_pi == -1 and beta_pi2 == -1
    # symbols at the inert prime q of Q(sqrt2): (z/q) = (N z / q)
    pistar_q = leg(-d, q)
    beta_q = leg(2, q)
    assert beta_q == -1 and bit(pistar_q) == c
    m = q * d
    assert m % 8 == 5                                      # sqrt2 inert in Q(sqrt2, sqrt m)
    # R : K = Q(sqrt2, sqrt(-m)); rows -1, pi*, pi'*; columns P_2, P_pi, P_pi'
    R = [
        [1, bit(leg(-1, d)), bit(leg(-1, d))],
        [u, bit(leg(q, d) * s), bit(s)],
        [u, bit(s), bit(leg(q, d) * s)],
    ]
    # R': F' = Q(sqrt(-m beta)); rows -q, pi*, pi'*; columns Q_q, P_pi, P_pi'
    Rp = [
        [bit(beta_q), bit(leg(-q, d)), bit(leg(-q, d))],
        [bit(pistar_q), bit(leg(q, d) * s * beta_pi), bit(s)],
        [bit(pistar_q), bit(s), bit(leg(q, d) * s * beta_pi2)],
    ]
    return c, rank_f2(R), rank_f2(Rp)


def main() -> None:
    from collections import Counter
    cnt = Counter()
    for fn in sys.argv[1:]:
        for row in csv.DictReader(open(fn)):
            cnt[check(int(row["q"]), int(row["d"]))] += 1
    for (c, rk, rkp), n in sorted(cnt.items()):
        print(f"(q/d) = {'-1' if c else '+1'}: rank R = {rk} (4-rank A(k_1) = {3 - rk}), "
              f"rank R' = {rkp} (4-rank A(F') = {3 - rkp}), pairs {n}")
    assert set(cnt) <= {(0, 1, 3), (1, 3, 2)}
    print("all symbol identities and ranks as proved")


if __name__ == "__main__":
    main()
