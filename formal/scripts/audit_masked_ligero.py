#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Exact audit calculations; neither a Lean theorem nor a production attack.

The numerical expression matches the Lean list-counting proof; the decimal
bit presentation is external arithmetic. The second budget includes GKR under
the stated circuit-shape bounds; noninteractive compilation is excluded.
"""

from collections import Counter
from fractions import Fraction
from math import comb, log2


def query_fraction(n, a, t):
    return Fraction(comb(a, t), comb(n, t)) if a >= t else Fraction(0)


def bits(error):
    return log2(error.denominator) - log2(error.numerator)


def counterexample():
    # Systematic nodes 0,1; W={1}; response nodes 0,1,2;
    # query nodes 3..7. Mask u(x)=(x-1)^3, false equation 0=1.
    # Enumerate ALL degree <=2 responses and classify by p(1)=alpha.
    prime = 101
    nodes = range(3, 8)
    mask = [pow(x - 1, 3, prime) for x in nodes]
    best = [0] * prime
    for c2 in range(prime):
        for c1 in range(prime):
            values = [(c2 * x * x + c1 * x) % prime for x in nodes]
            for c0 in range(prime):
                alpha = (c0 + c1 + c2) % prime
                matches = sum((v + c0) % prime == u for v, u in zip(values, mask))
                best[alpha] = max(best[alpha], matches)
    assert Counter(best) == {2: 92, 3: 9}
    actual = Fraction(sum(best), prime * len(nodes))
    sharp = query_fraction(5, 2, 1) + Fraction(1, prime)
    assert actual == Fraction(211, 505) > sharp == Fraction(207, 505)
    print(f"Toy masked test: {actual}; proposed sharp bound: {sharp}")


def list_bound():
    # Recorded fn-emulated layout, pq-20260924T203608Z-w7dyXU.
    gold = 2**64 - 2**32 + 1
    total = Fraction(703, 2**128) + Fraction(10502, gold**2)
    for name, n, k, field, a, code_terms in [
        ("H", 2272, 324, 2**128, 1222, 2),
        ("A", 3584, 512, gold**2, 1924, 1),
    ]:
        degree = 2 * k - 2
        agreement = a + 1
        denominator = agreement**2 - n * degree
        assert denominator > 0
        list_size = n * (agreement - degree) // denominator
        assert list_size == {"H": 46, "A": 75}[name]
        code = query_fraction(n, (n + k) // 2, 132)
        masked = query_fraction(n, a, 132)
        # AffineCodeTest proves N/|F|; the fixed list contributes L/|F|.
        error = Fraction(n + list_size, field) + code_terms * code + masked
        total += error
        print(f"{name}: a={a}, L<={list_size}, half bits={bits(error):.9f}")
    print(f"Combined list bound EXCLUDING GKR: {bits(total):.9f} bits")
    # Each source circuit: output/incoming dimensions <=40 and depth <=128.
    # GKRCircuitBudget proves this conservative numerator and the total bound.
    gkr_numerator = 2 * 40 + (2 + 5 * 40) * 128 + 1
    total += Fraction(gkr_numerator, 2**128) + Fraction(gkr_numerator, gold**2)
    assert total <= Fraction(1, 2**108)
    print(f"Including GKR (depth<=128, dimensions<=40): {bits(total):.9f} bits")


if __name__ == "__main__":
    counterexample()
    list_bound()
