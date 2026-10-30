"""Exact circle certificate for a fixed inverse-image polynomial of any degree.

For m=deg(P), write 6m=53k+ell, 0<=ell<53, and Q=P(1-z)^k.
If 2 max_circle|Q|+(r+1)^k <= A and A^53 (r+1)^ell <= exp(m wc),
then the per-N weight rate is wc for K=ceil(53N/m). The ceiling costs only a
fixed factor. Root removal is covered by the separate inverse-image lemma.
"""
import argparse,hashlib,json
from pathlib import Path
from fractions import Fraction as Q
from polynomial_circle_certificate import (
    exp_lower,circle_squared_polynomial,power_to_bernstein_on_minus_one_one,midpoint_split,
)

def large_exp_lower(x):
    assert x>0
    n=x.numerator//x.denominator;f=x-n
    e0=Q(2718281828459,10**12)
    assert e0<exp_lower(Q(1),50)
    tail=Q(1) if f==0 else exp_lower(f,40)
    return e0**n*tail

def integer_root_floor(n,k):
    assert isinstance(n,int) and n>=0 and isinstance(k,int) and k>0
    if n==0:return 0
    x=1<<((n.bit_length()+k-1)//k)
    while True:
        y=((k-1)*x+n//x**(k-1))//k
        if y>=x:break
        x=y
    while x**k>n:x-=1
    while (x+1)**k<=n:x+=1
    assert x**k<=n<(x+1)**k
    return x

def verify(path,wc=Q('51.71985'),radius=Q(100000001,100000000),max_depth=40):
    raw=Path(path).read_bytes();obj=json.loads(raw);m=obj['degree']
    cs=list(map(Q,obj['chebyshev_coefficients']))
    assert isinstance(m,int) and m>0 and len(cs)==m+1 and cs[-1]!=0
    assert 1<radius<2 and wc>0
    k,ell=divmod(6*m,53)
    power,mden=circle_squared_polynomial(cs,radius,k)
    bern,bden=power_to_bernstein_on_minus_one_one(power);degree=len(bern)-1
    el=large_exp_lower(m*wc);E=el.numerator//el.denominator
    arat=Q(E)/(radius+1)**ell
    A=integer_root_floor(arat.numerator//arat.denominator,53)
    assert A**53*(radius+1)**ell<=E
    H=(radius+1)**k
    assert A>H
    target=((Q(A)-H)/2)**2*mden*mden;tn,td=target.numerator,target.denominator
    stack=[(bern,0,0)];leaves=[]
    while stack:
        b,depth,index=stack.pop();den=bden<<(degree*depth)
        if max(b)*td<=tn*den:leaves.append([depth,index]);continue
        assert depth<max_depth and min(b)*td<=tn*den,('cap too small',depth,index)
        left,right=midpoint_split(b)
        stack.append((right,depth+1,2*index+1));stack.append((left,depth+1,2*index))
    endpoints=sorted((Q(i,1<<d),Q(i+1,1<<d)) for d,i in leaves);cursor=Q(0)
    for a,b in endpoints:assert a==cursor and a<b;cursor=b
    assert cursor==1
    return {'format':'catalan-general-polynomial-circle-v1','method':'exact integer autocorrelation and Bernstein subdivision',
      'witness_sha256':hashlib.sha256(raw).hexdigest(),'degree':m,'filter_degree':k,'remaining_filter_power':ell,
      'radius':str(radius),'weight_cap':str(wc),'A':str(A),'E':str(E),'num_pieces':len(leaves),
      'max_depth':max(d for d,i in leaves),'dyadic_pieces':leaves}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('witness',type=Path)
    p.add_argument('--weight-cap',default='51.71985');p.add_argument('--output',type=Path)
    a=p.parse_args();r=verify(a.witness,Q(a.weight_cap))
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in {'E','dyadic_pieces'}},indent=2))
