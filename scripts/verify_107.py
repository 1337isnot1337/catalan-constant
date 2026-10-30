#!/usr/bin/env python3
"""Check all finite certificates for the written bound 529.24599."""
import copy
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import asymmetric_residual
import inverse_image_certificate
import joint_polynomial_circle
import rank_profile
import residual_certificate
import verify_scalar_parameters as scalar

if not __debug__:
    raise RuntimeError('Run certificates without Python optimization flags.')


def verify_all():
    root = Path(__file__).resolve().parents[1]
    witness = root / 'certificates/inverse_image_107.json'
    parameters = json.loads((root / 'certificates/scalar_107.json').read_text())
    data = json.loads(witness.read_text())
    gain = rank_profile.verify()
    assert gain == scalar.GAIN
    branches = inverse_image_certificate.verify(data)
    assert branches['degree'] == 107
    circle = joint_polynomial_circle.verify(witness, Q(parameters['weight_cap']))
    assert circle['witness_sha256'] == hashlib.sha256(witness.read_bytes()).hexdigest()
    assert circle['degree'] == branches['degree']
    strips = residual_certificate.verify()
    positive = asymmetric_residual.verify()
    assert Q(data['gap_minus']) == Q(strips['gap'])
    assert Q(data['gap_plus']) == Q(positive['gap'])
    assert Q(strips['cap']) == Q(positive['cap']) == Q(parameters['residual_cap'])
    assert Q(parameters['near_cap']) == Q('-0.77')
    assert Q(circle['weight_cap']) == Q(parameters['weight_cap']) < Q(parameters['w'])
    gates = scalar.verify(parameters)
    bad = copy.deepcopy(data)
    bad['left_endpoint'] = '0'
    try:
        inverse_image_certificate.verify(bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError('Invalid permitted support was accepted.')
    try:
        scalar.verify(dict(parameters, exponent='529'))
    except AssertionError:
        pass
    else:
        raise RuntimeError('Exponent below the criterion threshold was accepted.')
    return {
        'result': 'All finite certificates passed',
        'scope': 'Written arbitrary-degree quadrature proof using cited upstream theorems',
        'irrationality_exponent_bound': parameters['exponent'],
        'inverse_branches': branches, 'circle': circle,
        'symmetric_residual_extension': strips,
        'positive_residual_extension': positive,
        'rank_profile_area': str(gain), 'scalar_gates': gates,
        'negative_controls': ['Invalid support rejected', 'Exponent below threshold rejected'],
    }


if __name__ == '__main__':
    print(json.dumps(verify_all(), indent=2))
