#!/usr/bin/env python3
"""Reproduce all new finite certificates for the current written bound."""
import argparse
import json
from pathlib import Path
from verify_107 import verify_all

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify_all()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: inverse branches, circle, residual fields, arithmetic profile, scalar gates')
    print('Written bound: mu(G) <=', result['irrationality_exponent_bound'])
    print('Exact threshold:', result['scalar_gates']['criterion_threshold'])
    print('Scope: new written quadrature argument; not a complete Lean build')
