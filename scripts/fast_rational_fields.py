"""Bounded-size exact rational intervals for residual-field certificates.

Series operations round outward to 112 binary fractional bits at each step.
This controls denominator growth without introducing floating-point decisions.
"""
from fractions import Fraction as Q
from residual_certificate import I

BITS=112
def rnd(x):return x.rounded(BITS)

def derivative_poly(center,cs):
    """Exact shifted derivative coefficients, using integer recurrences.

    If center=a/b, write U_k(center+y)=sum_j v[k,j] y^j/b^(k-j).
    The Chebyshev recurrence becomes v[k+1,j]=2a*v[k,j]+2*v[k,j-1]
    -b^2*v[k-1,j]. A common denominator combines the finite trial terms.
    """
    a,b=center.numerator,center.denominator
    scale=1<<40;ints=[c*scale for c in cs]
    assert all(c.denominator==1 for c in ints)
    ints=[c.numerator for c in ints];n=len(cs)-1
    assert n>=0
    bp=[b**j for j in range(n+1)]
    out=[0]*(n+1);prev=[];cur=[1]
    for k,c in enumerate(ints):
        fac=-2*c*bp[n-k]
        for j,v in enumerate(cur):out[j]+=fac*v
        nxt=[0]*(len(cur)+1)
        for j,v in enumerate(cur):nxt[j]+=2*a*v;nxt[j+1]+=2*v
        for j,v in enumerate(prev):nxt[j]-=b*b*v
        prev,cur=cur,nxt
    return [Q(v,scale*bp[n-j]) for j,v in enumerate(out)]

def log_core(y,n=32):
    assert 1<=y<=2
    t=rnd(I.point((y-1)/(y+1)));t2=rnd(t*t);p=t;s=I.point(0)
    for k in range(n):s=rnd(s+p/(2*k+1));p=rnd(p*t2)
    tail=2*p.hi/((2*n+1)*(1-t2.hi))
    assert t2.hi<1
    return (2*s+I(Q(0),tail)).rounded()

LOG2=log_core(Q(2))
def log_q(x):
    assert x>0;k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    return (log_core(x)+k*LOG2).rounded()

def atan_small(x,n=48):
    assert abs(x)<=Q(1,2)
    if x<0:return -atan_small(-x,n)
    t=rnd(I.point(x));t2=rnd(t*t);p=t;s=I.point(0)
    for k in range(n):s=rnd(s+((-1)**k)*p/(2*k+1));p=rnd(p*t2)
    e=p.hi/(2*n+1)
    return (s+(I(Q(0),e) if n%2==0 else I(-e,Q(0)))).rounded()

PI4=(4*atan_small(Q(1,5))-atan_small(Q(1,239))).rounded()
def atan_q(x):
    if x<0:return -atan_q(-x)
    if x<=Q(1,2):return atan_small(x)
    if x>2:return (2*PI4-atan_q(1/x)).rounded()
    return (PI4+atan_small((x-1)/(x+1))).rounded()

def argument_q(ar,ai):
    assert ar!=0 or ai!=0
    if ar>0:return atan_q(ai/ar)
    if ar<0:return ((4*PI4 if ai>=0 else -4*PI4)+atan_q(ai/ar)).rounded()
    return 2*PI4 if ai>0 else -2*PI4

def value(x,cs,tails):
    a=Q(1);b=x;finite=Q(0)
    for k,c in enumerate(cs,1):finite+=c*b/k;a,b=b,2*x*b-a
    v=-Q(53,58)*log_q(1+x*x)-2*finite
    for zr,zi,rr,ri in tails:
        ar=1+zr*zr-zi*zi-2*x*zr;ai=2*zr*zi-2*x*zi
        v+=rr/2*log_q(ar*ar+ai*ai)-ri*argument_q(ar,ai)
    return v.rounded()

def derivative(x,center,poly,tails):
    y=x-center;v=I.point(0)
    for c in reversed(poly):v=rnd(v*y+c)
    v=rnd(v-Q(106,58)*x/(1+x.square()))
    for zr,zi,rr,ri in tails:
        ar0=1+zr*zr-zi*zi;ar1=-2*zr;ai0=2*zr*zi;ai1=-2*zi
        ar=ar0+ar1*x;ai=ai0+ai1*x
        pr=rr*zr-ri*zi;pi=rr*zi+ri*zr
        q2=ar1*ar1+ai1*ai1;q1=2*(ar0*ar1+ai0*ai1);q0=ar0*ar0+ai0*ai0
        f=lambda a:q2*a*a+q1*a+q0
        vals=[f(x.lo),f(x.hi)]
        if q2>0:
            vertex=-q1/(2*q2)
            if x.lo<=vertex<=x.hi:vals.append(f(vertex))
        den=I(min(vals),max(vals));assert den.lo>0
        v=rnd(v-2*(pr*ar+pi*ai)/den)
    return v.rounded()
