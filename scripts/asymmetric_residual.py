"""Exact positive residual-strip extension, for optional asymmetric quadrature."""
import json
from fractions import Fraction as Q
from pathlib import Path
from residual_certificate import I,parse_trial,derivative_poly,derivative,value

def verify(gap=Q(857,10000),blocks=16,cells=8):
    assert 0<gap<Q(401,2500) and blocks>0 and cells>0
    cs,tails=parse_trial(Path(__file__).resolve().parents[1]/'certificates/trial_data.json')
    old=Q(401,2500);cap=-Q(315531,5000000)
    upper=None;lower=None
    for b in range(blocks):
        lo=gap+(old-gap)*b/blocks;hi=gap+(old-gap)*(b+1)/blocks
        center=(lo+hi)/2;poly=derivative_poly(center,cs)
        for j in range(cells):
            a=lo+(hi-lo)*j/cells;c=lo+(hi-lo)*(j+1)/cells
            d=derivative(I(a,c),center,poly,tails)
            assert d.hi<0,(b,j,d)
            upper=d.hi if upper is None else max(upper,d.hi)
            lower=d.lo if lower is None else min(lower,d.lo)
    v=value(gap,cs,tails)
    assert v.hi<cap
    return {'gap':str(gap),'old_gap':str(old),'cap':str(cap),'blocks':blocks,'cells_per_block':cells,'derivative_lower':str(lower),'derivative_upper':str(upper),'endpoint_lower':str(v.lo),'endpoint_upper':str(v.hi),'endpoint_margin':str(cap-v.hi)}

if __name__=='__main__':
    r=verify();print(json.dumps(r,indent=2))
