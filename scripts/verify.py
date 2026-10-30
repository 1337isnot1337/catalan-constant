#!/usr/bin/env python3
"""Reproduce every new finite certificate for the published written bound."""
import argparse
import copy
import json
from fractions import Fraction as Q
from pathlib import Path

import circle_certificate as circle
import rank_profile
import residual_certificate as residual
import scalar_certificate as scalar

if not __debug__:
    raise RuntimeError('Run certificates without Python optimization flags.')


def reject_bad_circle(cert):
    # Check that coverage and inequalities are enforced, not just parsed.
    for change in ('gap', 'inequality'):
        bad = copy.deepcopy(cert)
        if change == 'gap':
            bad['pieces'][0][0] = '1/1000000'
        else:
            bad['E'] = '1'
        try:
            circle.verify(bad)
        except AssertionError:
            pass
        else:
            raise RuntimeError('Malformed circle certificate was accepted: ' + change)


def verify_all():
    gain = rank_profile.verify()
    assert gain == scalar.GAIN
    circ = circle.generate(Q(1573, 10000), scalar.WC)
    circle.verify(circ)
    reject_bad_circle(circ)
    strips = residual.verify()
    gates = scalar.verify()
    assert Q(circ['gap']) == Q(strips['gap'])
    assert Q(strips['cap']) == scalar.RESIDUAL
    assert Q(circ['weight_cap']) == scalar.WC < scalar.W
    assert circ['degree'] == 53 and circ['filter_degree'] == 6
    return {
        'result': 'All new finite certificates passed',
        'scope': 'Written proof using cited upstream theorems; no new Lean build',
        'irrationality_exponent_bound': str(scalar.B),
        'circle': {key: circ[key] for key in ('gap', 'radius', 'weight_cap', 'E')},
        'circle_cells': len(circ['pieces']),
        'rank_profile': {'pieces': 102, 'area': str(gain)},
        'residual_strips': strips,
        'scalar_gates': gates,
        'negative_controls': 'Malformed coverage and false circle cap rejected',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify_all()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: exact profile area; circle cover; residual strips; scalar gates')
    print('PASS: malformed-certificate negative controls')
    print('Written bound: mu(G) <= 531.55361')
    print('Exact criterion threshold:', result['scalar_gates']['criterion_threshold'])
    print('Scope: upstream mathematical theorems + new exact rational certificates')
