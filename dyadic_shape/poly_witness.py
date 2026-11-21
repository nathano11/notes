"""Witness polynomials for congruence lemmas in Lean 4 core (no Mathlib).

A statement "expr % M = r" about integer polynomials is proved in two steps that
are stable across Lean 4.33.1 and 4.36.0:

    obtain <z, hz> : exists z, expr = M*z + r := <WITNESS, by grind>
    rw [hz]; omega

`grind` checks the ring identity and `omega` the linear arithmetic. The witness
is (expr - r)/M as a polynomial; this script computes it exactly and prints it
in Lean syntax, or fails if some coefficient is not divisible by M (then the
congruence is false as a polynomial identity and needs a case split first).

Example (the three cases of DyadicContent.inert_distance):

    python poly_witness.py
"""
from collections import defaultdict


class Poly:
    """Integer polynomial in named variables, as {exponent tuple: coefficient}."""

    def __init__(self, terms=None, names=()):
        self.names = tuple(names)
        self.terms = {k: v for k, v in (terms or {}).items() if v}

    @classmethod
    def variables(cls, names):
        names = tuple(names)
        out = []
        for i in range(len(names)):
            e = [0] * len(names)
            e[i] = 1
            out.append(cls({tuple(e): 1}, names))
        return out

    def _lift(self, other):
        if isinstance(other, Poly):
            return other
        return Poly({tuple([0] * len(self.names)): int(other)}, self.names)

    def __add__(self, other):
        other = self._lift(other)
        d = defaultdict(int)
        for k, v in self.terms.items():
            d[k] += v
        for k, v in other.terms.items():
            d[k] += v
        return Poly(d, self.names)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()}, self.names)

    def __sub__(self, other):
        return self + (-self._lift(other))

    def __rsub__(self, other):
        return self._lift(other) - self

    def __mul__(self, other):
        other = self._lift(other)
        d = defaultdict(int)
        for k, v in self.terms.items():
            for k2, v2 in other.terms.items():
                d[tuple(a + b for a, b in zip(k, k2))] += v * v2
        return Poly(d, self.names)

    __rmul__ = __mul__

    def lean(self):
        parts = []
        for k, v in sorted(self.terms.items()):
            factors = []
            for name, e in zip(self.names, k):
                factors += [name] * e
            mon = "*".join(factors)
            if len(factors) > 1:
                mon = "(" + mon + ")"
            if not mon:
                body = str(abs(v))
            elif abs(v) == 1:
                body = mon
            else:
                body = f"{abs(v)}*{mon}"
            parts.append((" - " if v < 0 else " + ") + body)
        text = "".join(parts)
        if not text:
            return "0"
        return text[3:] if text.startswith(" + ") else "-" + text[3:]


def witness(expr, modulus, residue):
    """The polynomial z with expr = modulus*z + residue, in Lean syntax."""
    q = expr - residue
    bad = [(k, v) for k, v in q.terms.items() if v % modulus]
    if bad:
        raise ValueError(f"not divisible by {modulus}: {bad}")
    return Poly({k: v // modulus for k, v in q.terms.items()}, q.names).lean()


if __name__ == "__main__":
    i, j, e, f, a = Poly.variables("ijefa")

    def n(a_, b_, c_, c1_):
        return 2 * a_ * a_ - c1_ * (a_ * b_) + c_ * (b_ * b_)

    print("inert, a odd b even :", witness(n(2 * i + 1, 2 * j, 4 * e + 2, 4 * f + 2), 4, 2))
    print("inert, a odd b odd  :", witness(n(2 * i + 1, 2 * j + 1, 4 * e + 2, 4 * f + 2), 4, 2))
    print("inert, a even b odd :", witness(n(2 * i, 2 * j + 1, 4 * e + 2, 4 * f + 2), 4, 2))
    print("eisenstein, b odd   :", witness(n(a, 2 * j + 1, 2 * e + 1, 4 * f), 2, 1))
    print("eisenstein, b even  :", witness(n(2 * i + 1, 2 * j, 2 * e + 1, 4 * f), 4, 2))
