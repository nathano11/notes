"""Marked relation at layer two: k_2 = Q(theta, sqrt(-m)), theta = zeta_16 + zeta_16^-1.

gamma is the automorphism zeta -> zeta^5 (theta -> 3 theta - theta^3) fixing
sqrt(-m).  For the 2-part c of the class of a degree-one prime, find every
(a, b) modulo E with

    gamma^2(c) + a gamma(c) + b c  in  {0, [p_2]},

where p_2 is the prime above 2, by principal-ideal tests on explicit ideals,
and compare with the set predicted from the analytic side (Stage B).

Usage: python test_layer2.py q d E [max_primes]
"""
import sys
import time

import shape_engine as E_
from cm_classgroup import CMField, RealField
from predict_stage_b import layer2, PREC


def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n


def build(m):
    Q2 = RealField([2, 0, -4, 0, 1])
    th = [0, 1, 0, 0]
    th3 = Q2.mul(th, Q2.mul(th, th))
    th6 = Q2.mul(th3, th3)
    pows = [[1, 0, 0, 0]]
    for _ in range(5):
        pows.append(Q2.mul(pows[-1], th))
    for bits in range(64):
        c = [sum(((bits >> i) & 1) * pows[i][j] for i in range(6)) for j in range(4)]
        val = Q2.mul(c, c)
        val[0] += m
        if Q2.divides(th6, val):
            break
    else:
        raise RuntimeError("no square root of -m modulo theta^6")
    t = Q2.exact_div([2 * x for x in c], th3)
    n = Q2.exact_div(val, th6)
    K = CMField(Q2, t, n)
    # gamma
    thp = [0, 3, 0, -1]

    def real_map(a):
        out, pw = [0, 0, 0, 0], [1, 0, 0, 0]
        for x in a:
            out = [o + x * p for o, p in zip(out, pw)]
            pw = Q2.mul(pw, thp)
        return out
    thp3 = Q2.mul(thp, Q2.mul(thp, thp))
    A0 = Q2.exact_div([x - y for x, y in zip(real_map(c), c)], thp3)
    B0 = Q2.exact_div(th3, thp3)
    gxi = A0 + B0
    mat, pw = [], [1, 0, 0, 0]
    imgs = []
    for _ in range(4):
        imgs.append(pw)
        pw = Q2.mul(pw, thp)
    for i in range(8):
        mat.append(K.lift(imgs[i]) if i < 4 else K.mul(K.lift(imgs[i - 4]), gxi))

    def act(v):
        return [sum(v[i] * mat[i][j] for i in range(8)) for j in range(8)]
    # sanity: order four, multiplicative, fixes sqrt(-m) = theta^3 xi - c
    x, y = [1, 2, 0, -1, 3, 0, 1, 1], [0, 1, 1, 0, -2, 1, 0, 2]
    assert act(K.mul(x, y)) == K.mul(act(x), act(y))
    assert act(act(act(act(x)))) == x and act(act(x)) != x
    sq = [-u for u in c] + th3
    assert act(sq) == sq and K.mul(sq, sq) == [-m, 0, 0, 0, 0, 0, 0, 0]
    return K, Q2, (mat, real_map)


def main():
    q, d, Emod = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    max_primes = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    m = q * d
    C0, C1, mod, p0, p2 = E_.iwasawa_coefficients(q, d, PREC + 1)
    c = E_.row(q, d, 2)
    hi2 = int((c[0] - c[2]) ** 2 + (c[1] - c[3]) ** 2)
    h = 2 * p0 * p2 * hi2
    hodd = odd_part(h)
    inv, e, pred = layer2(C0, C1)
    assert e == Emod, (e, Emod)
    pred = set(pred)
    K, Q2, gam = build(m)
    print(f"({q},{d}) m={m}: h(k_2)={h}, odd part {hodd}; predicted set modulo {e}: "
          f"{sorted(pred) if len(pred) <= 8 else str(len(pred)) + ' pairs'}", flush=True)
    P2 = K.power(K.ramified_prime(Q2.make_totally_positive([0, 1, 0, 0]), None), hodd)
    print("  [p_2] trivial:", K.is_principal(P2), " [p_2]^2 trivial:",
          K.is_principal(K.product(P2, P2)), flush=True)
    done, p = 0, 15
    while done < max_primes and p < 3000:
        p += 2
        if p % 16 not in (1, 15) or any(p % f == 0 for f in range(3, int(p ** 0.5) + 1, 2)):
            continue
        if m % p == 0:
            continue
        P = K.split_prime(p)
        if P is None:
            continue
        t0 = time.time()
        g0 = K.power(P, hodd)
        g1 = K.reduce(K.apply(gam, g0))[0]
        g2 = K.reduce(K.apply(gam, g1))[0]
        order = 1
        cur = g0
        while not K.is_principal(cur):
            cur = K.product(cur, cur)
            order *= 2
        A = [K.unit_ideal]
        B = [K.unit_ideal]
        for _ in range(e - 1):
            A.append(K.product(A[-1], g1))
            B.append(K.product(B[-1], g0))
        found = {}
        for a in range(e):
            Ta = K.product(g2, A[a])
            Ta2 = K.product(Ta, P2)
            for b in range(e):
                Bi = K.inverse(B[b])
                if K.equal(Ta, Bi):
                    found[(a, b)] = "0"
                elif K.equal(Ta2, Bi):
                    found[(a, b)] = "[p_2]"
        S = set(found)
        verdict = ("EQUAL to prediction" if S == pred else
                   "contains prediction (class is not a Lambda-generator)" if S > pred else
                   "DISAGREES with prediction")
        vals = sorted(set(found.values()))
        print(f"  p={p}: order of class {order}; solutions {sorted(S) if len(S) <= 8 else len(S)}"
              f" values {vals}; {verdict}; {time.time() - t0:.0f}s", flush=True)
        done += 1
    print("  totals:", K.stats, flush=True)


if __name__ == "__main__":
    main()
