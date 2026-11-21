"""Analytic engine for the dyadic towers k = Q(sqrt(-qd)), q = 3 (8), d = 7 (16).

Exact integer arithmetic only.  For m = qd and psi = (./q)(./d) (the even
character of Q(sqrt m)), the level-n Stickelberger row is

    c_j = -(1/m) * sum_{h=0}^{m-1} h * psi(t_j + D h),  t_j = 5^(-j) mod D,
    D = 2^(n+2),  0 <= j < 2^n,

and Phi(T) = sum_j c_j (1+T)^j  modulo ((1+T)^(2^n) - 1), where
L_2(u, psi) = 2 Phi(5^u - 1).  The distinguished factor P of Phi is
Mizusawa's polynomial T^2 + C1 T + C0.

The closed form used in bulk is c_j = -psi(D) * S(t_j * D^(-1) mod m) with
S(c) = sum_{0 <= x < c} psi(x); `row_bruteforce` evaluates the definition
directly and `selftest` compares the two.
"""
from __future__ import annotations

import numpy as np

MASK64 = (1 << 64) - 1


def legendre_table(p: int) -> np.ndarray:
    t = np.full(p, -1, dtype=np.int8)
    t[0] = 0
    x = np.arange(1, p, dtype=np.int64)
    t[(x * x) % p] = 1
    return t


def psi_table(q: int, d: int) -> np.ndarray:
    m = q * d
    return np.resize(legendre_table(q), m).astype(np.int64) * np.resize(legendre_table(d), m)


def prefix_sums(psi: np.ndarray) -> np.ndarray:
    s = np.zeros(len(psi) + 1, dtype=np.int64)
    np.cumsum(psi, out=s[1:])
    return s


def spoke_points(n: int) -> list[int]:
    """t_j = 5^(-j) mod 2^(n+2), j = 0 .. 2^n - 1."""
    D = 1 << (n + 2)
    inv5 = pow(5, -1, D)
    out, t = [], 1
    for _ in range(1 << n):
        out.append(t)
        t = t * inv5 % D
    return out


def row(q: int, d: int, n: int, S: np.ndarray | None = None) -> np.ndarray:
    """Stickelberger row c_0 .. c_{2^n-1} as int64."""
    m = q * d
    if S is None:
        S = prefix_sums(psi_table(q, d))
    D = 1 << (n + 2)
    Dinv = pow(D, -1, m)
    psiD = 1 if n % 2 == 0 else -1          # psi(2) = -1 because m = 5 (mod 8)
    idx = np.array([(t * Dinv) % m for t in spoke_points(n)], dtype=np.int64)
    return -psiD * S[idx]


def row_bruteforce(q: int, d: int, n: int) -> list[int]:
    m = q * d
    lq, ld = legendre_table(q), legendre_table(d)
    D = 1 << (n + 2)
    out = []
    for t in spoke_points(n):
        tot = 0
        for h in range(m):
            a = t + D * h
            tot += h * int(lq[a % q]) * int(ld[a % d])
        assert tot % m == 0
        out.append(-tot // m)
    return out


_BINOM_CACHE: dict[tuple[int, int], np.ndarray] = {}


def binom_matrix(n: int, K: int) -> np.ndarray:
    """B[j, i] = binom(j, i) mod 2^64 for j < 2^n, i < K."""
    key = (n, K)
    if key not in _BINOM_CACHE:
        B = np.zeros((1 << n, K), dtype=np.uint64)
        r = np.zeros(K, dtype=np.uint64)
        r[0] = 1
        for j in range(1 << n):
            B[j] = r
            nxt = r.copy()
            nxt[1:] += r[:-1]          # wraps mod 2^64, which is what we want
            r = nxt
        _BINOM_CACHE[key] = B
    return _BINOM_CACHE[key]


def taylor(c: np.ndarray, n: int, K: int) -> list[int]:
    """phi_i = sum_j c_j binom(j, i) mod 2^64, i < K."""
    B = binom_matrix(n, K)
    cu = c.astype(np.int64).astype(np.uint64)
    with np.errstate(over="ignore"):
        phi = cu @ B
    return [int(v) for v in phi]


def weierstrass(phi: list[int], bits: int = 64) -> tuple[int, int]:
    """Distinguished quadratic factor of sum phi_i T^i (lambda = 2, mu = 0).

    Fixed point of C0 + C1 T = (phi_0 + phi_1 T) / V(T) in Z/2^bits[T]/(T^2+C1 T+C0),
    V = sum_{i>=2} phi_i T^(i-2).  The series is truncated at len(phi); the
    tail lies in 2^floor(len(phi)/2) O.
    """
    M = 1 << bits
    if phi[0] % 2 or phi[1] % 2 or phi[2] % 2 == 0:
        raise ValueError("not of Weierstrass degree 2 with mu = 0")
    C0 = C1 = 0
    for _ in range(4 * bits):
        def mul(a, b):
            x, y = a
            u, v = b
            return ((x * u - C0 * y * v) % M, (x * v + u * y - C1 * y * v) % M)
        V = (0, 0)
        for i in range(len(phi) - 1, 1, -1):
            V = mul(V, (0, 1))
            V = ((V[0] + phi[i]) % M, V[1])
        v0, v1 = V
        nrm = (v0 * v0 - C1 * v0 * v1 + C0 * v1 * v1) % M
        conj = ((v0 - C1 * v1) % M, (-v1) % M)
        inv = pow(nrm, -1, M)
        Vinv = (conj[0] * inv % M, conj[1] * inv % M)
        new = mul((phi[0] % M, phi[1] % M), Vinv)
        if new == (C0, C1):
            break
        C0, C1 = new
    else:
        raise RuntimeError("Weierstrass iteration did not stabilise")
    return C0, C1


def iwasawa_coefficients(q: int, d: int, n: int, S: np.ndarray | None = None):
    """(C0 mod 2^(n-1), C1 mod 2^(n-1), 2^(n-1), Phi(0), Phi(-2)).

    Precision: P is determined by Phi modulo omega_n O with O = Z_2[T]/(P), and
    omega_n O is contained in 2^(n-1) O for n >= 2 in every type, so both
    coefficients are reported modulo 2^(n-1) (a safe common bound).
    """
    c = row(q, d, n, S)
    K = 2 * n + 6
    phi = taylor(c, n, K)
    C0, C1 = weierstrass(phi)
    mod = 1 << (n - 1)
    phi0 = int(c.sum())                                   # Phi(0)  = h(-4m)/2
    signs = np.where(np.arange(len(c)) % 2 == 0, 1, -1)
    phim2 = int((c * signs).sum())                        # Phi(-2) = h(-8m)/2
    return C0 % mod, C1 % mod, mod, phi0, phim2


def v2(x: int) -> int:
    if x == 0:
        return 10 ** 9
    return (x & -x).bit_length() - 1


def class_number_forms(D: int) -> int:
    """h(D), D < 0 fundamental, by counting reduced forms (a, b, c)."""
    assert D < 0 and D % 4 in (0, 1)
    h = 0
    b = D % 2
    while 3 * b * b <= -D:
        nn = (b * b - D) // 4
        lo = max(b, 1)
        hi = int(np.sqrt(nn))
        while hi * hi > nn:
            hi -= 1
        while (hi + 1) * (hi + 1) <= nn:
            hi += 1
        if hi >= lo:
            a = np.arange(lo, hi + 1, dtype=np.int64)
            a = a[nn % a == 0]
            if len(a):
                cc = nn // a
                single = (a == b) | (a == cc)
                if b == 0:
                    h += len(a)
                else:
                    h += int(single.sum()) + 2 * int((~single).sum())
        b += 2
    return h


def selftest() -> None:
    for (q, d, n) in [(3, 7, 3), (3, 23, 2), (11, 7, 2)]:
        assert list(row(q, d, n)) == row_bruteforce(q, d, n), (q, d, n)
    assert class_number_forms(-84) == 4 and class_number_forms(-168) == 4
    assert class_number_forms(-276) == 8 and class_number_forms(-23) == 3
    # Mizusawa p. 134: P = T^2 + 15604 T + 26266 (mod 2^15) for (3, 7)
    C0, C1, mod, p0, p2 = iwasawa_coefficients(3, 7, 17)
    assert mod >= 1 << 15
    assert (C0 % (1 << 15), C1 % (1 << 15)) == (26266, 15604), (C0, C1)
    assert 2 * p0 == class_number_forms(-84) and 2 * p2 == class_number_forms(-168)
    print("selftest ok: closed form = definition; (3,7) matches Mizusawa mod 2^15")


if __name__ == "__main__":
    selftest()
