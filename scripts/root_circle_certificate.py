#!/usr/bin/env python3
"""Exact circle bounds from rational enclosures of every real polynomial root.

The Decimal search only proposes brackets. Exact rational signs prove them.
Every circle decision uses rational arithmetic and an exponential lower bound.
The real part of z, rather than a trigonometric parameter, indexes each cell.
"""
import argparse
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
from polynomial_circle_certificate import chebyshev_to_power, exp_lower


def evaluate(coefficients, x):
    result = Q(0)
    for c in reversed(coefficients):
        result = c + x * result
    return result


def root_brackets(data, coefficients):
    result = []
    with localcontext() as ctx:
        ctx.prec = 120
        decimal_coefficients = [Decimal(c.numerator) / Decimal(c.denominator) for c in coefficients]
        def dec(x):
            return Decimal(x.numerator) / Decimal(x.denominator)
        def value(x):
            total = Decimal(0)
            for c in reversed(decimal_coefficients):
                total = c + x * total
            return total
        scale = 10**22
        for side in ['left_controls', 'right_controls']:
            controls = list(map(Q, data[side]))
            for a, b in zip(controls, controls[1:]):
                lo, hi = dec(a), dec(b)
                sign = value(lo) > 0
                for _ in range(90):
                    mid = (lo + hi) / 2
                    if (value(mid) > 0) == sign:
                        lo = mid
                    else:
                        hi = mid
                lower = Q(int((lo * scale).to_integral_value(rounding=ROUND_FLOOR)), scale)
                upper = Q(int((hi * scale).to_integral_value(rounding=ROUND_CEILING)), scale)
                assert a < lower < upper < b
                assert evaluate(coefficients, lower) * evaluate(coefficients, upper) < 0
                assert upper < 0 or lower > 0
                result.append((lower, upper))
    assert len(result) == data['degree']
    assert all(a[1] < b[0] for a, b in zip(result, result[1:]))
    return result


def certificate(path, wc=Q('52.18435'), progress=False):
    raw = Path(path).read_bytes()
    data = json.loads(raw)
    coefficients = chebyshev_to_power(list(map(Q, data['chebyshev_coefficients'])))
    m = data['degree']
    assert m == 130 and len(coefficients) == m + 1 and coefficients[-1] != 0
    roots = root_brackets(data, coefficients)
    radius = Q(100000001, 10**8)
    k, ell = divmod(6 * m, 53)
    assert k == 14 and ell == 38
    loghi = Q(693147180559945310, 10**18)
    j = int(float(2 * m * wc) / math.log(2))
    t = 2 * m * wc - j * loghi
    assert 0 <= t <= 1
    exponential_lower = Q(2)**j * exp_lower(t, 16)
    leaves = []
    stack = [(Q(-1), Q(1), 0, 0)]
    checked = 0
    while stack:
        unit_lo, unit_hi, depth, index = stack.pop()
        lo, hi = radius * unit_lo, radius * unit_hi
        product = coefficients[-1]**2
        for a, b in roots:
            x = hi if b < 0 else lo
            fa = radius**2 - 2 * a * x + a*a
            fb = radius**2 - 2 * b * x + b*b
            bound = max(fa, fb)
            assert bound > 0
            product *= bound
        distance_sq = radius**2 + 1 - 2 * lo
        assert distance_sq > 0
        product *= distance_sq**k
        M = math.isqrt(product.numerator // product.denominator) + 1
        assert Q(M*M) >= product
        h = distance_sq**(k//2)
        H = (h.numerator + h.denominator - 1) // h.denominator
        assert H >= h
        A = 2*M + H
        checked += 1
        if Q(A)**106 * distance_sq**ell <= exponential_lower:
            leaves.append({'depth': depth, 'index': index, 'M': str(M), 'H': str(H)})
        else:
            assert depth < 32, ('cap too small', depth, index)
            mid = (unit_lo + unit_hi) / 2
            stack.append((mid, unit_hi, depth + 1, 2*index + 1))
            stack.append((unit_lo, mid, depth + 1, 2*index))
        if progress and checked % 200 == 0:
            print('checked', checked, 'accepted', len(leaves), 'pending', len(stack), flush=True)
    cursor = Q(0)
    for a,b in sorted((Q(c['index'],2**c['depth']),Q(c['index']+1,2**c['depth'])) for c in leaves):
        assert a == cursor and a < b
        cursor = b
    assert cursor == 1
    return {
        'format': 'catalan-real-root-circle-v1',
        'witness_sha256': hashlib.sha256(raw).hexdigest(),
        'degree': m, 'radius': str(radius), 'filter_degree': k,
        'remaining_power': ell, 'weight_cap': str(wc),
        'root_intervals': [[str(a),str(b)] for a,b in roots],
        'binary_exponent': j, 'taylor_argument': str(t), 'taylor_terms': 16,
        'num_pieces': len(leaves), 'checked_cells': checked,
        'max_depth': max(c['depth'] for c in leaves), 'cells': leaves,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--progress', action='store_true')
    args = parser.parse_args()
    result = certificate(args.witness, progress=args.progress)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'cells','root_intervals'}}, indent=2))
