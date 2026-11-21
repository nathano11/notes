"""S5: the 2-class groups of k_1 = Q(sqrt2, sqrt(-m)) and F' = Q(sqrt(-m(2+sqrt2)))
by exhaustion over ideal classes (principal-ideal tests), compared with the
orders from the analytic class number formula and the predicted structure.

Usage: python test_quartic.py q d [q d ...]
"""
import sys
import time

import shape_engine as E
from cm_classgroup import CMField, RealField, invariant_factors, two_group


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def sqrt2_mod(d):
    return [t for t in range(d) if (t * t - 2) % d == 0]


def run(q, d):
    m = q * d
    F = RealField([-2, 0, 1])
    c = E.row(q, d, 2)
    p0, p2 = int(c.sum()), int(c[0] - c[1] + c[2] - c[3])
    hi2 = int((c[0] - c[2]) ** 2 + (c[1] - c[3]) ** 2)
    fields = {
        "k_1": (CMField(F, [0, 1], [(1 + m) // 2, 0]), 2 * p0 * p2),
        "F'": (CMField(F, [0, 0], [2 * m, m]), 2 * hi2),
    }
    res = {}
    for name, (K, h) in fields.items():
        t0 = time.time()
        hodd = odd_part(h)
        target = h // hodd
        ram = [K.ramified_prime([2, 1], None), K.ramified_prime([q, 0], (q + 1) // 2)]
        for r in sqrt2_mod(d):
            ram.append(K.ramified_prime(F.prime_generator(d, r), (d + 1) // 2))
        gens = [K.power(P, hodd) for P in ram]
        G, orders = two_group(K, gens)
        amb = len(G)
        p = 3
        while len(G) < target and p < 400:
            p += 2
            if p % 8 not in (1, 7) or any(p % f == 0 for f in range(3, int(p ** 0.5) + 1, 2)):
                continue
            if m % p == 0:
                continue
            P = K.split_prime(p)
            if P is None:
                continue
            gens.append(K.power(P, hodd))
            G, orders = two_group(K, gens)
        fac = invariant_factors(orders)
        res[name] = (fac, len(G), target, amb)
        print(f"({q},{d}) {name}: h = {h}, 2-part {target}; classes of ramified primes generate "
              f"a group of order {amb}; group found has order {len(G)} with invariant factors "
              f"{fac}; {K.stats['principal_tests']} principal-ideal tests, "
              f"{time.time() - t0:.1f}s", flush=True)
    return res


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    for i in range(0, len(a), 2):
        run(a[i], a[i + 1])
