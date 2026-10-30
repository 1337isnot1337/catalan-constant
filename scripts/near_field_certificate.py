"""Sharper eventual near-field cap from the exact first trial coefficient.

For N>=1,000,000, (48N-1)/(58N)>=(48-10^-6)/58. Since log(y)<0,
this replaces the near-field logarithmic coefficient by alpha=(48-10^-6)/58
for an upper bound. Its derivative has a strictly decreasing cubic numerator,
so a single exact root bracket plus rigorous logarithms certifies its maximum.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
from residual_certificate import parse_trial,log_q,LOG2

def verify():
    cs,tails=parse_trial(Path(__file__).resolve().parents[1]/'certificates/trial_data.json')
    u=cs[0]+sum(rr*zr-ri*zi for zr,zi,rr,ri in tails)
    epsilon=Q(1,1000000);alpha=(48-epsilon)/58
    cap=Q('-0.78145547')
    assert u>0 and 0<alpha<Q(106,58)
    def p(y):return alpha+(alpha-Q(106,58))*y*y-u*y-u*y*y*y
    assert p(Q(0))>0 and p(Q(1))<0
    # p'(y)=2(alpha-106/58)y-u-3uy^2<0 for all y>=0.
    lo=Q(0);hi=Q(1)
    for _ in range(80):
        mid=(lo+hi)/2
        if p(mid)>0:lo=mid
        else:hi=mid
    assert 0<lo<hi<1 and p(lo)>0 and p(hi)<0
    upper=-Q(53,58)*log_q(1+lo*lo).lo+alpha*log_q(hi).hi-u*lo
    assert upper<cap
    grouped_threshold=10000000
    grouped_upper=upper+LOG2.hi/(58*grouped_threshold)
    assert grouped_upper<cap
    return {'method':'exact rational cubic isolation and logarithm enclosures',
        'first_coefficient':str(u),'epsilon':str(epsilon),'alpha':str(alpha),
        'scale_threshold':1000000,'maximizer_lower':str(lo),'maximizer_upper':str(hi),
        'maximum_upper':str(upper),'near_cap':str(cap),'cap_margin':str(cap-upper),
        'grouped_scale_threshold':grouped_threshold,'grouped_maximum_upper':str(grouped_upper),
        'grouped_cap_margin':str(cap-grouped_upper)}

if __name__=='__main__':
    r=verify();print(json.dumps(r,indent=2))
