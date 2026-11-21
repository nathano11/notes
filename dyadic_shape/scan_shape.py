"""Scan of the family q = 3 (8), d = 7 (16) for the residue shape of P.

Usage: python scan_shape.py LO HI LEVEL OUT.csv
Writes one line per pair with LO < qd < HI:
    q,d,legendre(q/d),C0,C1,modulus,2*Phi(0),2*Phi(-2)
"""
import sys
import time

import numpy as np

import shape_engine as E


def primes_upto(N: int) -> np.ndarray:
    s = np.ones(N + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def main() -> None:
    lo, hi, n, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    P = primes_upto(hi // 3 + 1)
    qs = [int(p) for p in P if p % 8 == 3]
    ds = [int(p) for p in P if p % 16 == 7]
    pairs = sorted((q * d, q, d) for q in qs for d in ds if lo < q * d < hi)
    t0 = time.time()
    with open(out, "w") as f:
        f.write("q,d,leg,C0,C1,mod,h4m,h8m\n")
        for i, (m, q, d) in enumerate(pairs):
            S = E.prefix_sums(E.psi_table(q, d))
            C0, C1, mod, p0, p2 = E.iwasawa_coefficients(q, d, n, S)
            leg = 1 if pow(q, (d - 1) // 2, d) == 1 else -1
            f.write(f"{q},{d},{leg},{C0},{C1},{mod},{2 * p0},{2 * p2}\n")
            if i % 2000 == 0:
                print(i, len(pairs), round(time.time() - t0, 1), flush=True)
    print("pairs", len(pairs), "seconds", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
