#!/usr/bin/env python3
"""Check the asymmetric polynomial quadrature and its irrationality bound."""
import argparse
import copy
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import asymmetric_residual
import general_polynomial_circle
import inverse_image_certificate
import inverse_image_scalar_certificate as scalar
import rank_profile
import residual_certificate

if not __debug__:
    raise RuntimeError('Run certificates without Python optimization flags.')


def verify_all():
    root = Path(__file__).resolve().parents[1]
    witness = root / 'certificates/inverse_image_53.json'
    data = json.loads(witness.read_text())
    gain = rank_profile.verify()
    assert gain == scalar.GAIN
    branches = inverse_image_certificate.verify(data)
    assert branches['degree'] == 53
    bad = copy.deepcopy(data)
    bad['left_endpoint'] = '0'
    try:
        inverse_image_certificate.verify(bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError('Invalid permitted support was accepted.')
    circle = general_polynomial_circle.verify(witness, scalar.WC)
    assert circle['witness_sha256'] == hashlib.sha256(witness.read_bytes()).hexdigest()
    strips = residual_certificate.verify()
    positive = asymmetric_residual.verify()
    assert Q(data['gap_minus']) == Q(strips['gap'])
    assert Q(data['gap_plus']) == Q(positive['gap'])
    assert Q(strips['cap']) == Q(positive['cap']) == scalar.RESIDUAL
    assert Q(circle['weight_cap']) == scalar.WC < scalar.W
    gates = scalar.verify()
    return {
        'result': 'All asymmetric finite certificates passed',
        'scope': 'Written polynomial-quadrature proof using cited upstream theorems',
        'irrationality_exponent_bound': str(scalar.B),
        'inverse_branches': branches,
        'circle': circle,
        'symmetric_residual_extension': strips,
        'positive_residual_extension': positive,
        'rank_profile_area': str(gain),
        'scalar_gates': gates,
        'negative_control': 'Invalid permitted support rejected',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify_all()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: exact inverse branches, circle, residual fields, profile, scalar gates')
    print('Written bound: mu(G) <=', str(scalar.B))
    print('Exact threshold:', result['scalar_gates']['criterion_threshold'])
    print('Scope: new written quadrature argument; not a complete Lean build')
