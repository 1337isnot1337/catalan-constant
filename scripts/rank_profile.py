#!/usr/bin/env python3
"""Check the exact area of Litsey's published 102-piece nullity profile.

This checks the transcribed rational data and their integral. The claim that
the pieces bound nullities uses the cited upstream theorem wins532_cert.
"""
import json
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run certificates without Python optimization flags.')

EXPECTED = Q(36235515874601938601596598, 1642609663271115992578125)


def verify(path=None):
    if path is None:
        path = Path(__file__).resolve().parents[1] / 'certificates/rank_profile.json'
    data = json.loads(Path(path).read_text())
    assert data['source_commit'] == 'aa2a42f4f3835347ad46608779e22dd52c2dc7bf'
    assert data['columns'] == ['left', 'right', 'intercept', 'slope']
    assert len(data['rows']) == 102
    previous = Q(0)
    area = Q(0)
    for row in data['rows']:
        left, right, intercept, slope = map(Q, row)
        assert previous <= left < right <= 78
        assert intercept + slope * left >= 0
        assert intercept + slope * right >= 0
        area += intercept * (right-left) + slope * (right**2-left**2)/2
        previous = right
    assert area == EXPECTED == Q(data['exact_area'])
    return area


if __name__ == '__main__':
    area = verify()
    print(json.dumps({'verified': True, 'pieces': 102, 'exact_area': str(area),
                      'area_decimal_display': float(area)}, indent=2))
