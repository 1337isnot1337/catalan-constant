#!/usr/bin/env python3
"""Check all finite certificates for the written bound 528.23288."""
import copy
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import full_residual_certificate
import inverse_image_certificate
import joint_polynomial_circle
import near_field_certificate
import rank_profile
import verify_scalar_parameters as scalar

if not __debug__:
    raise RuntimeError('Run certificates without Python optimization flags.')


def verify_all():
    root = Path(__file__).resolve().parents[1]
    certs = root / 'certificates'
    witness = certs / 'inverse_image_trimmed_130.json'
    parameters = json.loads((certs / 'scalar_trimmed_130.json').read_text())
    support = json.loads((certs / 'residual_trimmed_parameters.json').read_text())
    data = json.loads(witness.read_text())
    gain = rank_profile.verify()
    assert gain == scalar.GAIN
    branches = inverse_image_certificate.verify(data)
    assert branches['degree'] == 130
    assert data['format'] == 'chebyshev-rational-inverse-image-v2'
    expected_support = [
        [-Q(data['outer_minus']), -Q(data['gap_minus'])],
        [Q(data['gap_plus']), Q(1)],
    ]
    assert [[Q(x) for x in row] for row in support['support_intervals']] == expected_support
    assert Q(support['residual_cap']) == Q(parameters['residual_cap'])
    circle = joint_polynomial_circle.verify(witness, Q(parameters['weight_cap']))
    assert circle['witness_sha256'] == hashlib.sha256(witness.read_bytes()).hexdigest()
    assert circle['degree'] == branches['degree']
    assert Q(circle['weight_cap']) == Q(parameters['weight_cap']) < Q(parameters['w'])
    residual = full_residual_certificate.verify(support)
    near = near_field_certificate.verify()
    assert Q(near['near_cap']) == Q(parameters['near_cap'])
    assert near['grouped_scale_threshold'] == 10000000
    gates = scalar.verify(parameters)
    bad = copy.deepcopy(data)
    bad['outer_minus'] = '1'
    try:
        inverse_image_certificate.verify(bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError('Invalid outer support endpoint was accepted.')
    try:
        scalar.verify(dict(parameters, exponent='528'))
    except AssertionError:
        pass
    else:
        raise RuntimeError('Exponent below the criterion threshold was accepted.')
    return {
        'result': 'All finite certificates passed',
        'scope': 'Written quadrature and eventual-energy proof using cited upstream theorems',
        'irrationality_exponent_bound': parameters['exponent'],
        'inverse_branches': branches, 'circle': circle,
        'full_residual_domain': residual, 'eventual_near_field': near,
        'rank_profile_area': str(gain), 'scalar_gates': gates,
        'negative_controls': ['Invalid support rejected', 'Exponent below threshold rejected'],
    }


if __name__ == '__main__':
    result = verify_all()
    print('PASS: all exact finite certificates for', result['irrationality_exponent_bound'])
