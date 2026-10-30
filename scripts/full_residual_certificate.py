"""Exact certificate for a residual cap on arbitrary rational support intervals.

Each accepted rational cell uses either a certified derivative sign and its
maximizing endpoint, or the mean-value bound R(mid)+h sup|R'|. No grid sample or
floating-point decision is used. The cells form an exact subdivision of the
requested intervals.
"""
import argparse,json
from fractions import Fraction as Q
from pathlib import Path
from residual_certificate import I,parse_trial
from fast_rational_fields import derivative_poly,derivative,value

def verify(data,progress=False):
    cap=Q(data['residual_cap']);support=[tuple(map(Q,x)) for x in data['support_intervals']]
    assert support and all(-1<=a<b<=1 for a,b in support)
    assert all(support[i][1]<support[i+1][0] for i in range(len(support)-1))
    cs,tails=parse_trial(Path(__file__).resolve().parents[1]/'certificates/trial_data.json')
    cache={};leaves=[];checked=0
    def val(x):
        if x not in cache:cache[x]=value(x,cs,tails)
        return cache[x]
    for index,(a,b) in enumerate(support):
        stack=[(a,b,0)]
        while stack:
            lo,hi,depth=stack.pop();mid=(lo+hi)/2;h=(hi-lo)/2
            poly=derivative_poly(mid,cs);d=derivative(I(lo,hi),mid,poly,tails);checked+=1
            if d.hi<=0:
                v=val(lo);bound=v.hi;method='decreasing';at=lo
            elif d.lo>=0:
                v=val(hi);bound=v.hi;method='increasing';at=hi
            else:
                v=val(mid);bound=v.hi+h*max(abs(d.lo),abs(d.hi));method='mean-value';at=mid
            assert v.lo<=cap,('a support point exceeds the cap',at,v,cap)
            if bound<=cap:
                leaves.append({'interval_index':index,'lo':str(lo),'hi':str(hi),'method':method,'evaluation_point':str(at),
                    'evaluation_upper':str(v.hi),'derivative_lower':str(d.lo),'derivative_upper':str(d.hi),'certified_upper':str(bound)})
            else:
                assert depth<50,('maximum depth reached',lo,hi)
                stack.append((mid,hi,depth+1));stack.append((lo,mid,depth+1))
            if progress and checked%20==0:print('checked',checked,'accepted',len(leaves),'pending',len(stack),flush=True)
    for index,(a,b) in enumerate(support):
        cells=sorted((Q(c['lo']),Q(c['hi'])) for c in leaves if c['interval_index']==index);cursor=a
        for lo,hi in cells:assert lo==cursor and lo<hi;cursor=hi
        assert cursor==b
    return {'format':'catalan-full-residual-v1','method':'exact rational derivative and logarithm enclosures',
        **data,'num_pieces':len(leaves),'checked_cells':checked,'cells':leaves}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('parameters',type=Path);p.add_argument('--output',type=Path);p.add_argument('--progress',action='store_true')
    a=p.parse_args();r=verify(json.loads(a.parameters.read_text()),a.progress)
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k!='cells'},indent=2))
