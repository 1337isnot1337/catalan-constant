"""Exact rational certificate extending Litsey's residual-field cap to gap .1573.

No floating-point arithmetic enters verify(). The only external premise is the
leader's already certified cap on 401/2500 <= abs(x) <= 1. This file certifies the
two extra closed strips using exact rational logarithm/argument enclosures and
the sign of the exact rational derivative. Data.lean is the upstream trial.
"""
import ast
import hashlib
import json
import re
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without -O: certificate assertions are required.')

UPSTREAM_SOURCE_SHA256='277927d0c5a685f403350405581cf178947352b53b2b28705d8d59a63c27c67b'
TRIAL_JSON_SHA256='73ab793c9eb1c115800d4e119284d39f8bcdabd8bb2b8dc147a081cdac120af2'

@dataclass(frozen=True)
class I:
    lo:Q
    hi:Q
    @staticmethod
    def point(x): return I(Q(x),Q(x))
    def __add__(a,b):
        if not isinstance(b,I):b=I.point(b)
        return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-coerce(b)
    def __rsub__(a,b):return coerce(b)+-a
    def __mul__(a,b):
        b=coerce(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def inv(a):
        assert not a.lo<=0<=a.hi
        return I(1/a.hi,1/a.lo)
    def __truediv__(a,b):return a*coerce(b).inv()
    def __rtruediv__(a,b):return coerce(b)*a.inv()
    def square(a):
        return I(Q(0) if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
    def rounded(a,bits=80):
        d=1<<bits
        return I(Q((a.lo.numerator*d)//a.lo.denominator,d),Q(-((-a.hi.numerator*d)//a.hi.denominator),d))

def coerce(x):return x if isinstance(x,I) else I.point(x)

def log_core(y,n=32):
    assert 1<=y<=2
    t=(y-1)/(y+1);t2=t*t;p=t;s=Q(0)
    for k in range(n):s+=p/(2*k+1);p*=t2
    return I(2*s,2*s+2*p/((2*n+1)*(1-t2))).rounded()

LOG2=log_core(Q(2))
def log_q(x):
    assert x>0
    k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    return (log_core(x)+k*LOG2).rounded()

def atan_small(x,n=48):
    assert abs(x)<=Q(1,2)
    if x<0:return -atan_small(-x,n)
    p=x;x2=x*x;s=Q(0)
    for k in range(n):s+=((-1)**k)*p/(2*k+1);p*=x2
    # Alternation remainder has the sign of the first omitted term.
    e=p/(2*n+1)
    return (I(s,s+e) if n%2==0 else I(s-e,s)).rounded()

PI4=(4*atan_small(Q(1,5))-atan_small(Q(1,239))).rounded()
def atan_q(x):
    if x<0:return -atan_q(-x)
    if x<=Q(1,2):return atan_small(x)
    if x>2:return (2*PI4-atan_q(1/x)).rounded()
    return (PI4+atan_small((x-1)/(x+1))).rounded()

def parse_trial(path):
    raw=Path(path).read_bytes()
    src=raw.decode('utf-8')
    if str(path).endswith('.json'):
        assert hashlib.sha256(raw).hexdigest()==TRIAL_JSON_SHA256
        obj=json.loads(src)
        assert obj['source_sha256']==UPSTREAM_SOURCE_SHA256
        cs=list(map(Q,obj['polynomial_coefficients']))
        tails=[tuple(map(Q,t)) for t in obj['geometric_terms']]
    else:
        assert hashlib.sha256(raw).hexdigest()==UPSTREAM_SOURCE_SHA256
        cs=[Q(v,2**40) for v in ast.literal_eval(re.search(r'def Pc : List ℤ := (\[[^]]+\])',src)[1])]
        block=re.search(r'def P : List TailQ := \[(.*?)\]\n',src,re.S)[1]
        tails=[tuple(Q(v) for v in re.findall(r'\(([^ ()]+) : ℚ\)',entry)) for entry in re.findall(r'⟨([^⟩]+)⟩',block)]
    assert len(cs)==160 and len(tails)==75
    assert all(zr*zr+zi*zi<1 for zr,zi,rr,ri in tails)
    assert cs[0]+sum(rr*zr-ri*zi for zr,zi,rr,ri in tails)>=Q(9,50)
    return cs,tails

def value(x,cs,tails):
    a=Q(1);b=x;finite=Q(0)
    for k,c in enumerate(cs,1):
        finite+=c*b/k
        a,b=b,2*x*b-a
    v=-Q(53,58)*log_q(1+x*x)-2*finite
    for zr,zi,rr,ri in tails:
        ar=1+zr*zr-zi*zi-2*x*zr
        ai=2*zr*zi-2*x*zi
        assert ar>0, 'principal argument needs explicit quadrant handling'
        v+=rr/2*log_q(ar*ar+ai*ai)-ri*atan_q(ai/ar)
    return v.rounded()

def add_poly(a,b):
    c=[Q(0)]*max(len(a),len(b))
    for j,v in enumerate(a):c[j]+=v
    for j,v in enumerate(b):c[j]+=v
    return c

def derivative_poly(center,cs):
    # U_0(center+y), U_1(center+y), ..., exact shifted power basis.
    um=[Q(0)];u=[Q(1)];out=[Q(0)]*len(cs)
    for c in cs:
        for j,v in enumerate(u):out[j]-=2*c*v
        un=add_poly([2*center*v for v in u],[Q(0)]+[2*v for v in u])
        un=add_poly(un,[-v for v in um]);um,u=u,un
    return out

def derivative(x,center,poly,tails):
    y=x-center;v=I.point(0)
    for c in reversed(poly):v=v*y+c
    v-=Q(106,58)*x/(1+x.square())
    for zr,zi,rr,ri in tails:
        ar=1+zr*zr-zi*zi-2*x*zr
        ai=2*zr*zi-2*x*zi
        pr=rr*zr-ri*zi;pi=rr*zi+ri*zr
        v+=-2*(pr*ar+pi*ai)/(ar.square()+ai.square())
    return v.rounded()

def verify(path=None,gap=Q(1573,10000),cells=32):
    if path is None:path=Path(__file__).resolve().parents[1]/'certificates/trial_data.json'
    cs,tails=parse_trial(path)
    old=Q(401,2500);cap=-Q(315531,5000000)
    assert isinstance(cells,int) and cells>0
    assert isinstance(gap,Q) and 0<gap<=old
    results={}
    for sign in [-1,1]:
        lo,hi=sorted([sign*gap,sign*old]);center=(lo+hi)/2
        poly=derivative_poly(center,cs)
        lower=None;upper=None
        for j in range(cells):
            a=lo+(hi-lo)*j/cells;b=lo+(hi-lo)*(j+1)/cells
            d=derivative(I(a,b),center,poly,tails)
            lower=d.lo if lower is None else min(lower,d.lo)
            upper=d.hi if upper is None else max(upper,d.hi)
            assert (d.lo>0 if sign==-1 else d.hi<0),(sign,j,d)
        endpoint=sign*gap;v=value(endpoint,cs,tails)
        assert v.hi<cap,(sign,v,cap)
        results[str(sign)]={'endpoint':str(endpoint),'value_lower':str(v.lo),'value_upper':str(v.hi),'derivative_lower':str(lower),'derivative_upper':str(upper),'cap_margin_lower':str(cap-v.hi)}
    return {'method':'exact rational intervals','gap':str(gap),'old_gap':str(old),'cap':str(cap),'cells_per_strip':cells,'strips':results}

if __name__=='__main__':
    result=verify()
    print(json.dumps(result,indent=2))
    for sign,r in result['strips'].items():
        print('display only:',sign,'R interval',float(Q(r['value_lower'])),float(Q(r['value_upper'])),'derivative',float(Q(r['derivative_lower'])),float(Q(r['derivative_upper'])))
