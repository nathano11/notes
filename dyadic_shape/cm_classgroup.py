"""Ideal classes in a CM field K = K+(xi), exact integer arithmetic.

Assumptions on K+ = Q(theta): Z[theta] is the maximal order, the class number
is one and every totally positive unit is a square (true for Q(sqrt 2) and
Q(zeta_16)^+, Weber).  O_K = O+ + O+ xi with xi^2 = t xi - n.

An ideal class is carried as (basis, nu): a Z-basis of an integral ideal a
(rows in the basis theta^i, theta^i xi) and a totally positive nu in O+ with
a * conj(a) = nu O_K.  Then

    a is principal  <=>  some alpha in a has alpha*conj(alpha) = nu
                    <=>  min_{alpha in a, alpha != 0} Tr_{K+/Q}(alpha conj(alpha)/nu) = [K+:Q],

because the trace of a totally positive integer of K+ is at least the degree,
with equality only for 1.  The minimum is found by integral LLL and exact
Fincke-Pohst enumeration.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt

import numpy as np


class RealField:
    def __init__(self, g):
        self.g = list(g)                      # monic, low -> high
        self.n = len(g) - 1
        self.roots = sorted(float(r.real) for r in np.roots(self.g[::-1]))
        one = [1] + [0] * (self.n - 1)
        self.one = one
        th = [0, 1] + [0] * (self.n - 2) if self.n > 1 else [0]
        pw, self.tr = one, []
        for _ in range(self.n):
            self.tr.append(sum(self.mulmat(pw)[i][i] for i in range(self.n)))
            pw = self.mul(pw, th)
        self.theta = th

    def mul(self, a, b):
        n = self.n
        c = [0] * (2 * n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    c[i + j] += x * y
        for k in range(2 * n - 2, n - 1, -1):
            t = c[k]
            if t:
                for i in range(n):
                    c[k - n + i] -= t * self.g[i]
        return c[:n]

    def mulmat(self, a):
        """M[i][j] = coefficient of theta^i in a*theta^j."""
        cols, pw = [], [1] + [0] * (self.n - 1)
        th = [0, 1] + [0] * (self.n - 2)
        for _ in range(self.n):
            cols.append(self.mul(a, pw))
            pw = self.mul(pw, th)
        return [[cols[j][i] for j in range(self.n)] for i in range(self.n)]

    def inv(self, a):
        n = self.n
        M = [[Fraction(x) for x in row] + [Fraction(1 if i == 0 else 0)]
             for i, row in enumerate(self.mulmat(a))]
        for c in range(n):
            p = next(r for r in range(c, n) if M[r][c] != 0)
            M[c], M[p] = M[p], M[c]
            M[c] = [x / M[c][c] for x in M[c]]
            for r in range(n):
                if r != c and M[r][c] != 0:
                    f = M[r][c]
                    M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        return [M[i][n] for i in range(n)]

    def norm(self, a):
        M = [[Fraction(x) for x in row] for row in self.mulmat(a)]
        n, det = self.n, Fraction(1)
        for c in range(n):
            p = next((r for r in range(c, n) if M[r][c] != 0), None)
            if p is None:
                return 0
            if p != c:
                M[c], M[p] = M[p], M[c]
                det = -det
            det *= M[c][c]
            for r in range(c + 1, n):
                f = M[r][c] / M[c][c]
                if f:
                    M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        assert det.denominator == 1
        return int(det)

    def adj(self, a):
        N = self.norm(a)
        v = [N * x for x in self.inv(a)]
        assert all(x.denominator == 1 for x in v)
        return [int(x) for x in v], N

    def trace(self, a):
        return sum(x * t for x, t in zip(a, self.tr))

    def signs(self, a):
        vals = [sum(float(x) * r ** i for i, x in enumerate(a)) for r in self.roots]
        assert all(abs(v) > 1e-9 for v in vals)
        return tuple(v > 0 for v in vals)

    def divides(self, a, b):
        """a | b in Z[theta]."""
        adj, N = self.adj(a)
        return all(x % N == 0 for x in self.mul(b, adj))

    def exact_div(self, b, a):
        adj, N = self.adj(a)
        w = self.mul(b, adj)
        assert all(x % N == 0 for x in w), "not divisible"
        return [x // N for x in w]

    def sign_fixers(self):
        """One unit for each sign pattern at the real places."""
        if hasattr(self, "_fix"):
            return self._fix
        fix, n = {}, self.n
        rng = range(-3, 4)
        import itertools
        for v in itertools.product(rng, repeat=n):
            if not any(v):
                continue
            if abs(self.norm(list(v))) == 1:
                fix.setdefault(self.signs(list(v)), list(v))
                if len(fix) == 2 ** n:
                    break
        assert len(fix) == 2 ** n, "not every sign pattern is a unit signature"
        self._fix = fix
        return fix

    def make_totally_positive(self, a):
        s = self.signs(a)
        return self.mul(a, self.sign_fixers()[s])    # unit with the same signs

    def prime_generator(self, p, t0):
        """Totally positive generator of (p, theta - t0), a prime of degree one."""
        n = self.n
        rows = [[p] + [0] * (n - 1)]
        for i in range(1, n):
            r = [0] * n
            r[0], r[i] = -pow(t0, i, p), 1
            rows.append(r)
        G = [[2 * self.trace(self.mul(x, y)) for y in rows] for x in rows]
        U, _, lam, d = lll_gram(G)
        red = [[sum(U[i][k] * rows[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        import itertools
        for bound in range(1, 12):
            for co in itertools.product(range(-bound, bound + 1), repeat=n):
                if max(abs(c) for c in co) != bound:
                    continue
                v = [sum(c * red[i][j] for i, c in enumerate(co)) for j in range(n)]
                if abs(self.norm(v)) == p:
                    return self.make_totally_positive(v)
        raise RuntimeError("no generator found")


def hnf(rows, N, D=None):
    """Row Hermite normal form of a full-rank lattice in Z^N.

    If D is given the lattice is assumed to contain D*Z^N; all arithmetic is then
    done modulo D, which keeps the entries bounded (no coefficient explosion)."""
    if D is not None:
        rows = [[x % D for x in r] for r in rows]
    rows = [list(r) for r in rows if any(r)]
    basis = []
    for col in range(N):
        cand = [r for r in rows if r[col] != 0]
        rest = [r for r in rows if r[col] == 0]
        if D is not None:
            e = [0] * N
            e[col] = D
            cand.append(e)
        while len(cand) > 1:
            cand.sort(key=lambda r: abs(r[col]))
            p = cand[0]
            new = [p]
            for r in cand[1:]:
                q = r[col] // p[col]
                r2 = [x - q * y for x, y in zip(r, p)]
                if D is not None:
                    r2 = [x % D for x in r2]
                if r2[col] != 0:
                    new.append(r2)
                elif any(r2):
                    rest.append(r2)
            cand = new
        if not cand:
            raise ValueError("lattice is not of full rank")
        p = cand[0]
        if p[col] < 0:
            p = [-x for x in p]
        basis.append(p)
        rows = rest
    for i in range(N):
        for k in range(i):
            q = basis[k][i] // basis[i][i]
            if q:
                basis[k] = [x - q * y for x, y in zip(basis[k], basis[i])]
    return basis


def lll_gram(G):
    """Integral LLL (Cohen, Algorithm 2.6.7) on an integral Gram matrix.
    Returns U (rows = new basis in the old one), the new Gram matrix, lambda, d."""
    n = len(G)
    G = [list(r) for r in G]
    U = [[int(i == j) for j in range(n)] for i in range(n)]
    lam = [[0] * n for _ in range(n)]
    d = [0] * n

    def D(i):
        return 1 if i < 0 else d[i]

    def addrow(k, l, q):                      # b_k -= q b_l
        U[k] = [a - q * b for a, b in zip(U[k], U[l])]
        G[k] = [a - q * b for a, b in zip(G[k], G[l])]
        for i in range(n):
            G[i][k] -= q * G[i][l]

    def red(k, l):
        if 2 * abs(lam[k][l]) > d[l]:
            q = (2 * lam[k][l] + d[l]) // (2 * d[l])
            addrow(k, l, q)
            lam[k][l] -= q * d[l]
            for i in range(l):
                lam[k][i] -= q * lam[l][i]

    def swap(k):
        U[k], U[k - 1] = U[k - 1], U[k]
        G[k], G[k - 1] = G[k - 1], G[k]
        for r in G:
            r[k], r[k - 1] = r[k - 1], r[k]
        for j in range(k - 1):
            lam[k][j], lam[k - 1][j] = lam[k - 1][j], lam[k][j]
        l = lam[k][k - 1]
        B = (D(k - 2) * d[k] + l * l) // d[k - 1]
        for i in range(k + 1, kmax + 1):
            t = lam[i][k]
            lam[i][k] = (d[k] * lam[i][k - 1] - l * t) // d[k - 1]
            lam[i][k - 1] = (B * t + l * lam[i][k]) // d[k]
        d[k - 1] = B

    d[0] = G[0][0]
    k, kmax = 1, 0
    while k < n:
        if k > kmax:
            kmax = k
            for j in range(k + 1):
                u = G[k][j]
                for i in range(j):
                    u = (d[i] * u - lam[k][i] * lam[j][i]) // D(i - 1)
                if j < k:
                    lam[k][j] = u
                else:
                    d[k] = u
            assert d[k] > 0, "Gram matrix is not positive definite"
        red(k, k - 1)
        if 4 * d[k] * D(k - 2) < 3 * d[k - 1] * d[k - 1] - 4 * lam[k][k - 1] ** 2:
            swap(k)
            k = max(1, k - 1)
        else:
            for l in range(k - 2, -1, -1):
                red(k, l)
            k += 1
    return U, G, lam, d


def short_vectors(G, lam, d, bound):
    """All nonzero x (up to sign) with x^T G x <= bound, for an LLL-reduced G."""
    n = len(G)
    B = [Fraction(d[i], 1 if i == 0 else d[i - 1]) for i in range(n)]
    mu = [[Fraction(lam[i][j], d[j]) for j in range(i)] for i in range(n)]
    out, x = [], [0] * n

    def rec(i, budget):
        if i < 0:
            if any(x):
                out.append(list(x))
            return
        c = -sum(mu[j][i] * x[j] for j in range(i + 1, n))
        r = budget / B[i]
        w = isqrt(int(r)) + 2
        lo, hi = int(c) - w - 1, int(c) + w + 1
        for xi in range(lo, hi + 1):
            cost = B[i] * (xi - c) ** 2
            if cost <= budget:
                x[i] = xi
                rec(i - 1, budget - cost)
        x[i] = 0

    rec(n - 1, Fraction(bound))
    seen, res = set(), []
    for v in out:
        key = tuple(v)
        neg = tuple(-a for a in v)
        if neg not in seen:
            seen.add(key)
            res.append(v)
    return res


class CMField:
    def __init__(self, Kp: RealField, t, n):
        self.Kp, self.g, self.N = Kp, Kp.n, 2 * Kp.n
        self.t, self.n = list(t), list(n)
        self.one = [1] + [0] * (self.N - 1)
        g = self.g
        self.basis = []
        for i in range(self.N):
            e = [0] * self.N
            e[i] = 1
            self.basis.append(e)
        self.unit_ideal = ([list(e) for e in self.basis], [1] + [0] * (g - 1))
        self.stats = {"principal_tests": 0, "products": 0}

    # ---- elements
    def mul(self, x, y):
        g, K = self.g, self.Kp
        a, b, c, d = x[:g], x[g:], y[:g], y[g:]
        bd = K.mul(b, d)
        re = [p - q for p, q in zip(K.mul(a, c), K.mul(self.n, bd))]
        im = [p + q + r for p, q, r in zip(K.mul(a, d), K.mul(b, c), K.mul(self.t, bd))]
        return re + im

    def conj(self, x):
        g, K = self.g, self.Kp
        a, b = x[:g], x[g:]
        return [p + q for p, q in zip(a, K.mul(self.t, b))] + [-q for q in b]

    def lift(self, a):
        return list(a) + [0] * self.g

    def twice_real(self, z):
        """z + conj(z) in O+."""
        g = self.g
        return [2 * p + q for p, q in zip(z[:g], self.Kp.mul(self.t, z[g:]))]

    def norm_to_real(self, x):
        z = self.mul(x, self.conj(x))
        assert not any(z[self.g:])
        return z[:self.g]

    # ---- ideals with their norm generator
    def ideal_norm(self, rows):
        p = 1
        for i in range(self.N):
            p *= rows[i][i]
        return p

    def gram(self, A):
        rows, nu = A
        adj, Nn = self.Kp.adj(nu)
        cj = [self.conj(r) for r in rows]
        N = self.N
        G = [[0] * N for _ in range(N)]
        for i in range(N):
            for j in range(i, N):
                w = self.Kp.mul(self.twice_real(self.mul(rows[i], cj[j])), adj)
                tr = self.Kp.trace(w)
                assert tr % Nn == 0
                G[i][j] = G[j][i] = tr // Nn
        return G

    def reduce(self, A):
        """Equivalent ideal of small norm; returns (ideal, principal?)."""
        rows, nu = A
        G = self.gram(A)
        U, G2, lam, d = lll_gram(G)
        g = self.g
        self.stats["principal_tests"] += 1
        best = None
        vecs = short_vectors(G2, lam, d, 2 * g)
        for v in vecs:
            if sum(v[i] * G2[i][j] * v[j] for i in range(self.N) for j in range(self.N)) == 2 * g:
                best = v
                break
        principal = best is not None
        if best is None:
            best = [1] + [0] * (self.N - 1)
        coeff = [sum(best[i] * U[i][k] for i in range(self.N)) for k in range(self.N)]
        alpha = [sum(coeff[k] * rows[k][j] for k in range(self.N)) for j in range(self.N)]
        if principal:
            assert self.norm_to_real(alpha) == list(nu)
            return self.unit_ideal, True
        adj, Nn = self.Kp.adj(nu)
        ca = self.conj(alpha)
        scale = self.mul(ca, self.lift(adj))
        new = []
        for r in rows:
            w = self.mul(scale, r)
            assert all(x % Nn == 0 for x in w)
            new.append([x // Nn for x in w])
        nu2 = self.Kp.exact_div(self.norm_to_real(alpha), nu)
        return (hnf(new, self.N, abs(self.Kp.norm(nu2))), nu2), False

    def is_principal(self, A):
        return self.reduce(A)[1]

    def product(self, A, B):
        self.stats["products"] += 1
        ra, na = A
        rb, nb = B
        rows = [self.mul(x, y) for x in ra for y in rb]
        bound = self.ideal_norm(ra) * self.ideal_norm(rb)
        return self.reduce((hnf(rows, self.N, bound), self.Kp.mul(na, nb)))[0]

    def inverse(self, A):
        rows, nu = A
        return (hnf([self.conj(r) for r in rows], self.N, self.ideal_norm(rows)), nu)

    def equal(self, A, B):
        ra, na = A
        rb, nb = self.inverse(B)
        rows = [self.mul(x, y) for x in ra for y in rb]
        bound = self.ideal_norm(ra) * self.ideal_norm(rb)
        return self.is_principal((hnf(rows, self.N, bound), self.Kp.mul(na, nb)))

    def power(self, A, e):
        R, base = self.unit_ideal, A
        while e:
            if e & 1:
                R = self.product(R, base)
            e >>= 1
            if e:
                base = self.product(base, base)
        return R

    def apply(self, M, A):
        """Image under a field automorphism given by its integral matrix M
        (M[i] = image of the i-th basis element) and its restriction to K+."""
        mat, real_map = M
        rows, nu = A
        new = [[sum(r[i] * mat[i][j] for i in range(self.N)) for j in range(self.N)] for r in rows]
        return (hnf(new, self.N, self.ideal_norm(rows)), real_map(nu))

    # ---- prime ideals
    def split_prime(self, p):
        """A prime of degree one over p, or None."""
        K, g = self.Kp, self.g
        for t0 in range(p):
            if sum(c * pow(t0, i, p) for i, c in enumerate(K.g)) % p:
                continue
            tt = sum(c * pow(t0, i, p) for i, c in enumerate(self.t)) % p
            nn = sum(c * pow(t0, i, p) for i, c in enumerate(self.n)) % p
            for r in range(p):
                if (r * r - tt * r + nn) % p == 0:
                    rows = [[p] + [0] * (self.N - 1)]
                    for i in range(1, self.N):
                        val = pow(t0, i, p) if i < g else pow(t0, i - g, p) * r % p
                        e = [0] * self.N
                        e[0], e[i] = -val, 1
                        rows.append(e)
                    return (hnf(rows, self.N, p), K.prime_generator(p, t0))
        return None

    def ramified_prime(self, varpi, half=None):
        """The prime above the ramified prime (varpi) of K+, varpi totally positive.
        `half`: an integer inverse of 2 modulo varpi, or None in residue characteristic 2."""
        K, g = self.Kp, self.g
        if half is None:
            r = None
            for cand in ([0] * g, [1] + [0] * (g - 1)):
                val = [a - b + c for a, b, c in zip(K.mul(cand, cand), K.mul(self.t, cand), self.n)]
                if K.divides(varpi, val):
                    r = cand
            assert r is not None
        else:
            r = [half * x for x in self.t]
        xi_r = [-x for x in r] + [1] + [0] * (g - 1)
        rows = [self.mul(self.lift(varpi), e) for e in self.basis]
        rows += [self.mul(xi_r, e) for e in self.basis]
        H = hnf(rows, self.N, abs(K.norm(varpi)))
        assert self.ideal_norm(H) == abs(K.norm(varpi)), (self.ideal_norm(H), K.norm(varpi))
        return (H, list(varpi))


def two_group(K: CMField, gens, target_order=None, log=None):
    """Subgroup generated by the given classes, by exhaustion with principal tests.
    Returns the list of elements and the multiset of their orders."""
    G = [K.unit_ideal]

    def find(x):
        return any(K.equal(x, y) for y in G)

    for g in gens:
        if find(g):
            continue
        powers, cur = [K.unit_ideal], g
        while not find(cur):
            powers.append(cur)
            cur = K.product(cur, g)
        G = [K.product(x, p) if p is not K.unit_ideal else x for p in powers for x in G]
        if log:
            log(f"  subgroup order {len(G)}")
        if target_order and len(G) >= target_order:
            break
    orders = []
    for x in G:
        o, cur = 1, x
        while not K.is_principal(cur):
            cur = K.product(cur, cur)
            o *= 2
        orders.append(o)
    return G, orders


def invariant_factors(orders):
    """Invariant factors of a finite abelian 2-group from its element orders."""
    size = len(orders)
    out, j, prev = [], 1, 1
    counts = []
    while True:
        cnt = sum(1 for o in orders if o <= 2 ** j)
        counts.append(cnt)
        if cnt == size:
            break
        j += 1
    # |A[2^j]| / |A[2^(j-1)]| = 2^(number of factors of exponent >= j)
    ranks, prev = [], 1
    for cnt in counts:
        q = cnt // prev
        ranks.append(q.bit_length() - 1)
        prev = cnt
    fac = []
    for j, rk in enumerate(ranks, start=1):
        nxt = ranks[j] if j < len(ranks) else 0
        fac += [2 ** j] * (rk - nxt)
    return sorted(fac)
