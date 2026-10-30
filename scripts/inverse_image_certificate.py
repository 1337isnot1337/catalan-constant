#!/usr/bin/env python3
"""Exact rational witness for all inverse branches of a polynomial on two bands.

The candidate generator reads floating-point search output, but the verifier
uses only exact rational arithmetic. A successful verification proves every
level in [-1,1] has degree(P) simple real preimages in the permitted bands.
"""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run this exact verifier without Python's -O optimization flag")


def chebyshev_value(coefficients, x):
    """Evaluate sum_k coefficients[k] T_k(x), exactly."""
    x=Q(x)
    a,b=Q(1),x
    total=Q(coefficients[0])
    for c in coefficients[1:]:
        total+=Q(c)*b
        a,b=b,2*x*b-a
    return total


def generate(candidate_path):
    candidate=json.loads(Path(candidate_path).read_text())
    gm=Q(1573,10000);gp=Q(857,10000)
    left=-2*gm/(1+gm*gm);right=2*gp/(1+gp*gp)
    coefficients=[Q(str(x))*Q(1000001,1000000) for x in candidate['cheb_coeffs']]
    critical=[Q(str(x)) for x in candidate['control_points']]
    left_points=sorted(set([Q(-1),left]+[x for x in critical if -1<x<left]))
    right_points=sorted(set([right,Q(1)]+[x for x in critical if right<x<1]))
    # The search output also contains approximations to the exact endpoints.
    # Discard these, keeping the exact rational endpoint instead.
    eps=Q(1,10**12)
    left_points=[x for x in left_points if x in [Q(-1),left] or min(abs(x+1),abs(x-left))>eps]
    right_points=[x for x in right_points if x in [right,Q(1)] or min(abs(x-right),abs(x-1))>eps]
    return {'format':'chebyshev-rational-inverse-image-v1',
            'degree':len(coefficients)-1,
            'gap_minus':str(gm),'gap_plus':str(gp),
            'left_endpoint':str(left),'right_endpoint':str(right),
            'chebyshev_coefficients':[str(x) for x in coefficients],
            'left_controls':[str(x) for x in left_points],
            'right_controls':[str(x) for x in right_points]}


def verify(c):
    assert c['format']=='chebyshev-rational-inverse-image-v1'
    co=list(map(Q,c['chebyshev_coefficients']))
    m=c['degree'];assert len(co)==m+1 and co[-1]!=0
    gm=Q(c['gap_minus']);gp=Q(c['gap_plus'])
    assert 0<gm<1 and 0<gp<1
    left=-2*gm/(1+gm*gm);right=2*gp/(1+gp*gp)
    assert Q(c['left_endpoint'])==left and Q(c['right_endpoint'])==right
    root_count=0;minimum=None;counts={}
    for name,lo,hi in [('left',Q(-1),left),('right',right,Q(1))]:
        xs=list(map(Q,c[name+'_controls']))
        assert len(xs)>=2 and xs[0]==lo and xs[-1]==hi
        assert all(a<b for a,b in zip(xs,xs[1:]))
        ys=[chebyshev_value(co,x) for x in xs]
        assert all(abs(y)>1 for y in ys)
        assert all(a*b<0 for a,b in zip(ys,ys[1:]))
        margin=min(abs(y)-1 for y in ys)
        minimum=margin if minimum is None else min(minimum,margin)
        counts[name]=len(xs)-1;root_count+=len(xs)-1
    assert root_count==m
    return {'verified':True,'degree':m,'root_counts':counts,
            'smallest_control_margin':str(minimum)}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidate',type=Path)
    p.add_argument('--verify',type=Path)
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    if a.verify:c=json.loads(a.verify.read_text())
    else:
        assert a.candidate is not None
        c=generate(a.candidate)
    result=verify(c)
    if a.output:a.output.write_text(json.dumps(c,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
