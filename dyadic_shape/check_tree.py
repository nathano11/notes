"""Checks for the consolidation in Dyadic_Residue_Shape.md, sections 6 and 7.

O = Z_2[T]/(T^2 + C1 T + C0), Y = O with basis (1, T), X = m = (2, T) with basis
(2, T).  For w = A + B T in m the matrix of w : Y -> X is
[[A/2, -C0 B/2], [B, A - C1 B]].

Part 1  Smith form against content and the form n = 2a^2 - c1 ab + c b^2, exact
        integers (the statement of DyadicContent.strict_smith).
Part 2  Random 2-adic coefficients of each residue shape, 40 binary digits:
        Smith exponents of X / w_{a,r} Y against the table of Appendix A.2, the
        valuation rule of Theorem 6, the ideal identities, the path of the
        vertex, and the conductor of Z_2[gamma^(2^a)].
Part 3  The same on actual fields: the pairs of scan_5000_1e6.csv (9 digits),
        and (3,7), (3,23), (11,263), (227,23), (739,7), (11,503) at 13 digits.
Part 4  Wheels, the golden unit and Fibonacci numbers; the ramified field of
        shape I.

Usage: python check_tree.py [scan.csv]
"""
import csv
import random
import sys
from math import gcd

random.seed(20261121)


def v2(x, cap):
    if x == 0:
        return cap
    return min(cap, (x & -x).bit_length() - 1)


class Order:
    def __init__(self, C0, C1, N):
        self.C0, self.C1, self.N, self.mod = C0, C1, N, 1 << N

    def mul(self, x, y):
        m = self.mod
        return ((x[0] * y[0] - self.C0 * x[1] * y[1]) % m,
                (x[0] * y[1] + x[1] * y[0] - self.C1 * x[1] * y[1]) % m)

    def gamma_pow(self, a):
        g = (1, 1)
        for _ in range(a):
            g = self.mul(g, g)
        return g

    def omega(self, a, s):
        g = self.gamma_pow(a)
        return ((g[0] - pow(s, 1 << a, self.mod)) % self.mod, g[1])

    def factor(self, j, s):
        """Phi_0 = (1+T) - s, Phi_j = (1+T)^(2^(j-1)) + s^(2^(j-1))."""
        if j == 0:
            return ((1 - s) % self.mod, 1)
        g = self.gamma_pow(j - 1)
        return ((g[0] + pow(s, 1 << (j - 1), self.mod)) % self.mod, g[1])

    def smith(self, w):
        """Exponents (e1, e2) of X/wY, or None if the precision does not decide."""
        A, B = w
        assert A % 2 == 0
        cap = self.N - 1
        half = (A // 2) % (1 << cap)
        ent = [half, (self.C0 // 2) * B, B, A - self.C1 * B]
        e1 = min(v2(x % (1 << cap), cap) for x in ent)
        det = (half * (A - self.C1 * B) + (self.C0 // 2) * B * B) % (1 << cap)
        vd = v2(det, cap)
        if vd >= cap - 1:
            return None
        return (e1, vd - e1)

    def norm_val(self, w):
        A, B = w
        return v2((A * A - self.C1 * A * B + self.C0 * B * B) % self.mod, self.N)

    def profile(self, s):
        tau, dl = (2 - self.C1) % self.mod, (1 - self.C1 + self.C0) % self.mod
        f = lambda z: (z * z - tau * z + dl) % self.mod
        k, l = v2(f(s), self.N), v2(f(-s % self.mod), self.N)
        h = v2(((dl - s * s) ** 2 + s * s * tau * tau) % self.mod, self.N)
        return k, l, h


def table_A2(a, k, l, h):
    m, M = min(k, l), max(k, l)
    if a == 0:
        return (0, k - 1)
    if a == 1:
        return (m - 1, M)
    if k >= 2 and l >= 2:
        return (m + a - 2, M + a - 1)
    assert k == 1 and l == 1
    return (-(-h // 2) + a - 2, h // 2 + a - 1)


def shape_of(C0, C1):
    if C0 % 4 == 2 and C1 % 4 == 0:
        return "I"
    if C0 % 8 == 4 and C1 % 4 == 2:
        return "IIa"
    if C0 % 8 == 0 and C1 % 4 == 2:
        return "IIb"
    return "other"


def split_roots(C0, C1, N):
    """Roots T0 = 0, T1 = 2 (mod 4) of P in Z_2 for shape IIb, modulo 2^(N-2)."""
    hh, ee = (C1 // 2), (C0 // 4)
    prec = N - 2
    out = []
    for u in (0, 1):
        for _ in range(prec + 2):
            val = (u * u + hh * u + ee) % (1 << prec)
            der = (2 * u + hh) % (1 << prec)
            u = (u - val * pow(der, -1, 1 << prec)) % (1 << prec)
        out.append((2 * u) % (1 << prec))
    return out


def dlog5(x, N):
    """r modulo 2^(N-2) with 5^r = x modulo 2^N, for x = 1 (mod 4)."""
    r, mod = 0, 1 << N
    for i in range(N - 2):
        if (pow(5, r, mod) - x) % (1 << (i + 3)) != 0:
            r += 1 << i
    assert (pow(5, r, mod) - x) % mod == 0
    return r


def check_pair(C0, C1, N, weights, layers, tally):
    O = Order(C0 % (1 << N), C1 % (1 << N), N)
    sh = shape_of(C0, C1)
    cap = N - 1
    roots = split_roots(C0, C1, N) if sh == "IIb" else None
    # conductor of Z_2[gamma^(2^a)]
    vt = v2((2 - C1) % O.mod, N)
    for a in range(1, max(layers) + 1):
        vb = v2(O.gamma_pow(a)[1], N)
        if vt + a - 1 < N - 1:
            tally["conductor"] += 1
            assert vb == a - 1 + vt, ("conductor", C0, C1, a, vb, vt)
    for r in weights:
        s = pow(5, -r, O.mod)
        k, l, h = O.profile(s)
        for a in layers:
            w = O.omega(a, s)
            sm = O.smith(w)
            if sm is None:
                tally["precision-limited"] += 1
                continue
            tally["tested"] += 1
            # (i) Appendix A.2
            if max(k, l, h) < N - 1:
                assert sm == table_A2(a, k, l, h), ("A2", C0, C1, r, a, sm, (k, l, h))
                tally["A2"] += 1
            # (ii) Theorem 6
            if sh == "I":
                wv = O.norm_val(w)
                assert sm == ((wv - 1) // 2, wv - 1 - (wv - 1) // 2), ("I", C0, C1, r, a)
                assert sm == [(0, 0), (0, 1)][a] if a < 2 else sm == (a, a)
                # ideal: w O = 2^a m for a >= 2, 2 O for a = 1, m for a = 0
                A, B = w
                if a >= 2:
                    assert v2(B, N) == a and v2(A, N) >= a + 1
                elif a == 1:
                    assert v2(A, N) == 1 and v2(B, N) >= 1
                # path: each of Phi_0, Phi_1, Phi_2 flips, later factors do not
                flips = [O.norm_val(O.factor(j, s)) for j in range(a + 1)]
                assert flips == ([1, 1, 3] + [2] * a)[:a + 1], ("I path", flips)
                tally["rule I"] += 1
            elif sh == "other" and C0 % 4 == 2:
                # Eisenstein with C1 = 2 (mod 4): same rule, nu_1 = nu_2 = v(N w)/2
                wv = O.norm_val(w)
                assert sm == ((wv - 1) // 2, wv - 1 - (wv - 1) // 2), ("(2,2)", C0, C1, r, a)
                tally["rule (2,2)"] += 1
            elif sh == "IIa":
                assert sm == (a, a + 1), ("IIa", C0, C1, r, a, sm)
                A, B = w
                if a >= 1:
                    assert v2(A, N) == a + 1 and v2(B, N) >= a + 1
                # path on the first wheel: Phi/2 modulo 2 in F_4 = {1, U, U+1}
                turn = []
                for j in range(a + 1):
                    FA, FB = O.factor(j, s)
                    turn.append(((FA // 2) % 2, FB % 2))
                assert turn == ([(0, 1), (1, 1)] + [(1, 0)] * a)[:a + 1], ("IIa path", turn)
                tally["rule IIa"] += 1
            elif sh == "IIb":
                pm = 1 << (N - 2)
                vals = [v2((pow(1 + t, 1 << a, pm) - pow(s, 1 << a, pm)) % pm, N - 2)
                        for t in roots]
                if max(vals) < N - 3:
                    assert sm == (min(vals) - 1, max(vals)), ("IIb", C0, C1, r, a, sm, vals)
                    tally["rule IIb"] += 1
                    # the two real spokes move the vertex in opposite senses
                    steps = []
                    for j in range(min(a, 2) + 1):
                        FA, FB = O.factor(j, s)
                        fv = [v2((FA + FB * t) % pm, N - 2) for t in roots]
                        steps.append(fv[0] - fv[1])
                    if a >= 1 and max(k, l) < N - 5:
                        # Phi_0 moves the vertex k - 2 steps one way, Phi_1 moves it
                        # l - 2 steps the other way, Phi_2 does not move it
                        assert steps[0] == k - 2 and steps[1] == -(l - 2), ("IIb path", steps, k, l)
                        if a >= 2:
                            assert steps[2] == 0
                        tally["path IIb"] += 1
                    r0 = (-dlog5((1 + roots[0]) % (1 << (N - 2)), N - 2))
                    r1 = (-dlog5((-(1 + roots[1])) % (1 << (N - 2)), N - 2))
                    kk = 3 + v2((r - r0) % (1 << (N - 4)), N - 4)
                    ll = 3 + v2((r - r1) % (1 << (N - 4)), N - 4)
                    if max(kk, ll) < N - 5:
                        assert (k, l) == (kk, ll), ("zeros", C0, C1, r, (k, l), (kk, ll))
                        tally["zeros"] += 1
    return sh


def part1():
    n_ok = 0
    for _ in range(20000):
        g = random.randint(1, 40)
        while True:
            a, b = random.randint(-60, 60), random.randint(-60, 60)
            if gcd(a, b) == 1:
                break
        c, c1 = random.randint(-30, 30), 2 * random.randint(-15, 15)
        C0, A, B = 2 * c, 2 * g * a, g * b
        M = [A // 2, -C0 * B // 2, B, A - c1 * B]
        d1 = gcd(gcd(M[0], M[1]), gcd(M[2], M[3]))
        det = M[0] * M[3] - M[1] * M[2]
        n = 2 * a * a - c1 * a * b + c * b * b
        assert d1 == g and det == g * g * n
        n_ok += 1
    print(f"Part 1: content g and form n give the Smith form, {n_ok} random integer cases")


def random_coefficients(shape, N):
    mod = 1 << N
    if shape == "I":
        return (4 * random.randrange(mod // 4) + 2) % mod, (4 * random.randrange(mod // 4)) % mod
    if shape == "IIa":
        return (8 * random.randrange(mod // 8) + 4) % mod, (4 * random.randrange(mod // 4) + 2) % mod
    if shape == "IIb":
        # plant zeros close to small odd weights so that large valuations occur
        r0 = random.choice([random.randrange(mod), random.randrange(1, 40, 2) + (1 << random.randint(3, 12)) * random.randrange(mod)])
        r1 = random.choice([random.randrange(mod), random.randrange(1, 40, 2) + (1 << random.randint(3, 12)) * random.randrange(mod)])
        z0, z1 = pow(5, -r0, mod), (-pow(5, -r1, mod)) % mod
        tau, dl = (z0 + z1) % mod, (z0 * z1) % mod
        C1 = (2 - tau) % mod
        return (dl - 1 + C1) % mod, C1
    if shape == "(0,0)":
        return (4 * random.randrange(mod // 4)) % mod, (4 * random.randrange(mod // 4)) % mod
    return (4 * random.randrange(mod // 4) + 2) % mod, (4 * random.randrange(mod // 4) + 2) % mod


def part2():
    N = 40
    for shape, count in (("I", 400), ("IIa", 400), ("IIb", 600), ("(0,0)", 300), ("(2,2)", 300)):
        tally = dict.fromkeys(["tested", "precision-limited", "A2", "rule I", "rule IIa",
                               "rule IIb", "rule (2,2)", "path IIb", "zeros", "conductor"], 0)
        for _ in range(count):
            C0, C1 = random_coefficients(shape, N)
            if shape in ("I", "IIa", "IIb"):
                assert shape_of(C0, C1) == shape
            weights = [2 * random.randrange(500) + 1 for _ in range(6)] + list(range(1, 40, 6))
            check_pair(C0, C1, N, weights, range(0, 6), tally)
        print(f"Part 2 [{shape}], {count} random coefficient pairs at {N} digits:",
              {k: v for k, v in tally.items() if v})


def part3(path):
    tally = dict.fromkeys(["tested", "precision-limited", "A2", "rule I", "rule IIa",
                           "rule IIb", "rule (2,2)", "path IIb", "zeros", "conductor"], 0)
    shapes = {"I": 0, "IIa": 0, "IIb": 0, "other": 0}
    fields = {1: 0, 3: 0, 5: 0, 7: 0}
    with open(path) as fh:
        for row in csv.DictReader(fh):
            C0, C1, mod = int(row["C0"]), int(row["C1"]), int(row["mod"])
            N = mod.bit_length() - 1
            sh = check_pair(C0, C1, N, range(1, 16, 2), range(0, 4), tally)
            shapes[sh] += 1
            if sh == "I":
                u = (((C1 // 2) ** 2 - C0) // 2) % 8
                fields[u] += 1
    print(f"Part 3, {sum(shapes.values())} fields of {path} at 9 digits: shapes {shapes};",
          {k: v for k, v in tally.items() if v})
    print("        shape I, ramified field Q_2(sqrt(2u)), u mod 8 -> count:", fields,
          "(u = 1: sqrt 2, 3: sqrt 6, 5: sqrt 10, 7: sqrt -2)")
    import shape_engine as E
    tally = dict.fromkeys(tally, 0)
    for q, d in ((3, 7), (3, 23), (11, 263), (227, 23), (739, 7), (11, 503)):
        C0, C1, mod, _, _ = E.iwasawa_coefficients(q, d, 14)
        N = mod.bit_length() - 1
        sh = check_pair(C0, C1, N, range(1, 40, 2), range(0, 6), tally)
        print(f"        ({q},{d}): (C0, C1) = ({C0}, {C1}) mod 2^{N}, shape {sh}")
    print("        six named fields at 13 digits:", {k: v for k, v in tally.items() if v})


def part4():
    # wheel sizes: lattices L in Z_2^2 with Z_2^2/L cyclic of order 2^n = points of P^1(Z/2^n)
    for n in range(1, 8):
        m = 1 << n
        pts = set()
        for x in range(m):
            for y in range(m):
                if x % 2 or y % 2:
                    pts.add(min(((u * x) % m, (u * y) % m) for u in range(1, m, 2)))
        assert len(pts) == 3 * 2 ** (n - 1)
    print("Part 4: wheel n has 3*2^(n-1) vertices, n = 1..7")
    # Fibonacci: phi^k = F_k phi + F_(k-1)
    F = [0, 1]
    while len(F) < 3 * 2 ** 14 + 2:
        F.append(F[-1] + F[-2])
    for k in range(1, 3 * 2 ** 12):
        v = v2(F[k], 10 ** 6)
        if k % 3:
            assert v == 0
        elif k % 6 == 3:
            assert v == 1
        elif k % 12 == 6:
            assert v == 3
        else:
            assert v == v2(k, 99) + 2
    appar, pisano = [], []
    for n in range(1, 13):
        m = 1 << n
        appar.append(next(k for k in range(1, len(F)) if F[k] % m == 0))
        pisano.append(next(k for k in range(1, len(F) - 1) if F[k] % m == 0 and F[k + 1] % m == 1))
    assert appar == [3, 6, 6] + [3 * 2 ** (n - 2) for n in range(4, 13)]
    assert pisano == [3 * 2 ** (n - 1) for n in range(1, 13)]
    print("        v_2(F_k) rule for k < 12288; rank of apparition of 2^n:", appar[:8],
          "; Pisano period 3*2^(n-1), n = 1..12")
    # the wheel group W_n = (Z[phi]/2^n)^x / (Z/2^n)^x and the orbit of phi on wheel n
    for n in range(1, 8):
        m = 1 << n
        mul = lambda x, y: ((x[0] * y[0] + x[1] * y[1]) % m, (x[0] * y[1] + x[1] * y[0] + x[1] * y[1]) % m)
        canon = lambda x: min(((u * x[0]) % m, (u * x[1]) % m) for u in range(1, m, 2))
        units = {canon((x, y)) for x in range(m) for y in range(m) if (x * x + x * y + y * y) % 2}
        assert len(units) == 3 * 2 ** (n - 1)
        one = canon((1, 0))
        order = {}
        for g in units:
            k, p = 1, g
            while canon(p) != one:
                p, k = mul(p, g), k + 1
            order[g] = k
        two_torsion = sum(1 for g in units if order[g] <= 2)
        expo = max(order.values())
        phi_orbit = order[canon((0, 1))]
        if n >= 3:
            assert (two_torsion, expo, phi_orbit) == (4, 3 * 2 ** (n - 2), 3 * 2 ** (n - 2))
        elif n == 2:
            assert (two_torsion, expo, phi_orbit) == (2, 6, 6)
        else:
            assert (two_torsion, expo, phi_orbit) == (1, 3, 3)
    print("        W_n is cyclic of order 3 (n=1), 6 (n=2), and Z/3 x Z/2 x Z/2^(n-2) for n = 3..7;",
          "phi has orbit 3, 6, then 3*2^(n-2): half of the wheel")
    # the golden unit inside the order of (3,23): phi = x + y U with U = T/2
    import shape_engine as E
    C0, C1, mod, _, _ = E.iwasawa_coefficients(3, 23, 14)
    N = mod.bit_length() - 3
    m = 1 << N
    hh, ee = (C1 // 2) % m, (C0 // 4) % m
    assert hh % 2 == 1 and ee % 2 == 1 and (hh * hh - 4 * ee) % 8 == 5
    umul = lambda x, y: ((x[0] * y[0] - ee * x[1] * y[1]) % m, (x[0] * y[1] + x[1] * y[0] - hh * x[1] * y[1]) % m)
    sols = []
    for start in ((0, 1), (1, 1)):
        x = start
        for _ in range(N + 2):
            fx = umul(x, x)
            fx = ((fx[0] - x[0] - 1) % m, (fx[1] - x[1]) % m)
            der = ((2 * x[0] - 1) % m, (2 * x[1]) % m)
            # inverse of der in Z_2[U]: der * conj / norm
            conj = ((der[0] - hh * der[1]) % m, (-der[1]) % m)
            nrm = (der[0] * der[0] - hh * der[0] * der[1] + ee * der[1] * der[1]) % m
            inv = tuple((c * pow(nrm, -1, m)) % m for c in conj)
            step = umul(fx, inv)
            x = ((x[0] - step[0]) % m, (x[1] - step[1]) % m)
        chk = umul(x, x)
        assert chk == ((x[0] + 1) % m, x[1])
        sols.append(x)
    print(f"        (3,23): the golden unit acts on the module: phi = {sols[0][0]} + {sols[0][1]}*(T/2)"
          f" and its conjugate {sols[1][0]} + {sols[1][1]}*(T/2) modulo 2^{N}; phi^2 = phi + 1 checked")


if __name__ == "__main__":
    part1()
    part2()
    part3(sys.argv[1] if len(sys.argv) > 1 else "scan_5000_1e6.csv")
    part4()
    print("ALL CHECKS PASSED")
