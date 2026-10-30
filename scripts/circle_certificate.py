#!/usr/bin/env python3
"""Construct and verify an exact rational certificate for the quadrature circle.

This mirrors the elementary inequalities in Litsey's CircPiece.ok. All decisions
use Fraction and integer arithmetic. Floating point is used only when printing
an informational decimal. It does not enter the certificate or its verifier.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this exact verifier without Python's -O optimization flag")


def sqrt_upper(x: Q, precision: int = 12) -> Q:
    """A strict rational upper bound for sqrt(x), verified by squaring."""
    assert x >= 0
    den = 10**precision
    out = Q(isqrt((x.numerator * den * den) // x.denominator) + 1, den)
    assert out >= 0 and out * out >= x
    return out


def exp_lower(x: Q, terms: int = 400) -> Q:
    """Positive Taylor polynomial below exp(x), for x > 0."""
    assert x > 0 and terms > 0
    total = term = Q(1)
    for k in range(1, terms):
        term *= x / k
        total += term
    return total


def piece(lo: Q, hi: Q, a: Q, radius: Q) -> tuple[Q, ...]:
    b1 = sqrt_upper((radius**2 + 1)**2 - 4 * lo**2)
    b2 = sqrt_upper((radius**2 + a**2)**2 - 4 * a**2 * lo**2)
    H = (b1 + b2) / (1 - a**2)
    base = H + sqrt_upper(H**2 - 1)
    return lo, hi, b1, b2, H, base


def valid_piece(p: tuple[Q, ...], a: Q, r: Q, E: Q) -> bool:
    lo, hi, b1, b2, H, base = p
    return (
        Q(0) <= lo <= hi <= r
        and b1 >= 0
        and b2 >= 0
        and (r*r + 1)**2 - 4*lo*lo <= b1*b1
        and (r*r + a*a)**2 - 4*a*a*lo*lo <= b2*b2
        and b1 + b2 <= H * (1-a*a)
        and H >= 1
        and base >= H
        and H*H - 1 <= (base-H)**2
        and Q(1) <= base <= Q(9)
        and base**53 * (r*r + 1 + 2*hi)**6 <= E
    )


def generate(gap: Q, wc: Q) -> dict:
    a = 2*gap / (1 + gap*gap)
    r = Q(100000001, 100000000)
    terms = 400
    elo = exp_lower(2*wc, terms)
    E = Q(elo.numerator // elo.denominator)
    pieces = []
    pending = [(Q(0), r, 0)]
    while pending:
        lo, hi, depth = pending.pop()
        p = piece(lo, hi, a, r)
        if valid_piece(p, a, r, E):
            pieces.append(p)
        else:
            if depth >= 40:
                raise ValueError("The requested exponent is too small for this cover")
            mid = (lo + hi)/2
            pending.append((mid, hi, depth+1))
            pending.append((lo, mid, depth+1))
    return {
        "format": "catalan-circle-rational-v1",
        "gap": str(gap), "a": str(a), "radius": str(r),
        "weight_cap": str(wc), "E": str(E), "C_squared": "9",
        "degree": 53, "filter_degree": 6, "exp_terms": terms,
        "pieces": [[str(x) for x in p] for p in pieces],
    }


def verify(c: dict) -> None:
    assert c["format"] == "catalan-circle-rational-v1"
    gap, a, r, wc, E = (Q(c[k]) for k in ["gap", "a", "radius", "weight_cap", "E"])
    assert 0 < gap < 1 and a == 2*gap/(1+gap*gap)
    assert 0 < a < 1 and 1-a*a <= 4*a and 1 < r <= 2
    assert c["degree"] == 53 and c["filter_degree"] == 6
    assert Q(c["C_squared"]) == 9
    assert 0 < E <= exp_lower(2*wc, c["exp_terms"])
    previous = Q(0)
    assert len(c["pieces"]) > 0
    for raw in c["pieces"]:
        p = tuple(Q(x) for x in raw)
        assert len(p) == 6 and p[0] == previous and p[0] < p[1]
        assert valid_piece(p, a, r, E)
        previous = p[1]
    assert previous == r


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--gap", default="1573/10000")
    p.add_argument("--weight-cap", default="526055/10000")
    p.add_argument("--output", type=Path)
    p.add_argument("--verify", type=Path)
    args = p.parse_args()
    if args.verify:
        c = json.loads(args.verify.read_text())
    else:
        c = generate(Q(args.gap), Q(args.weight_cap))
    verify(c)
    if args.output:
        args.output.write_text(json.dumps(c, indent=2) + "\n")
    print(json.dumps({"verified": True, "pieces": len(c["pieces"]),
                      "gap": c["gap"], "radius": c["radius"],
                      "weight_cap": c["weight_cap"], "E": c["E"]}, indent=2))


if __name__ == "__main__":
    main()
