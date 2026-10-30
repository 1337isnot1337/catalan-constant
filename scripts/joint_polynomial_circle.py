"""Exact inverse-image circle bound retaining the residual filter per cell.

Write 6m=53k+ell and Q=P(1-z)^k. A cell upper bound M on |Q| gives
2|Q|+|1-z|^k <= A=2ceil(M)+ceil((r+1)^k). On that cell check
A^106 * max_cell(|1-z|^2)^ell <= exp(2m wc).
All decisions use integers and rationals; no floating-point evaluations occur.
"""
import argparse,hashlib,json,math
from pathlib import Path
from fractions import Fraction as Q
from general_polynomial_circle import large_exp_lower
from polynomial_circle_certificate import circle_squared_polynomial,power_to_bernstein_on_minus_one_one,midpoint_split

def verify(path,wc=Q('51.70935'),radius=Q(100000001,100000000),max_depth=40):
    raw=Path(path).read_bytes();obj=json.loads(raw);m=obj['degree'];cs=list(map(Q,obj['chebyshev_coefficients']))
    assert isinstance(m,int) and m>0 and len(cs)==m+1 and cs[-1]!=0
    assert 1<radius<2 and wc>0
    k,ell=divmod(6*m,53);power,mden=circle_squared_polynomial(cs,radius,k)
    bern,bden=power_to_bernstein_on_minus_one_one(power);degree=len(bern)-1
    e=large_exp_lower(2*m*wc);E=e.numerator//e.denominator
    h=(radius+1)**k;H=-((-h.numerator)//h.denominator)
    stack=[(bern,0,0)];leaves=[]
    while stack:
        b,depth,index=stack.pop();den=(bden<<(degree*depth))*mden*mden
        bmax=max(b);assert bmax>=0
        M=math.isqrt(bmax//den)+1
        assert M*M*den>=bmax
        A=2*M+H
        lo=Q(2*index,1<<depth)-1
        filter_sq=radius*radius+1-2*radius*lo
        assert filter_sq>0
        if A**106*filter_sq.numerator**ell<=E*filter_sq.denominator**ell:
            leaves.append([depth,index]);continue
        assert depth<max_depth,('depth limit or cap too small',depth,index)
        left,right=midpoint_split(b);stack.append((right,depth+1,2*index+1));stack.append((left,depth+1,2*index))
    intervals=sorted((Q(i,1<<d),Q(i+1,1<<d)) for d,i in leaves);cursor=Q(0)
    for a,b in intervals:assert a==cursor and a<b;cursor=b
    assert cursor==1
    return {'format':'catalan-joint-polynomial-circle-v1','method':'exact autocorrelation and Bernstein subdivision with cell filter',
      'witness_sha256':hashlib.sha256(raw).hexdigest(),'degree':m,'filter_degree':k,'remaining_filter_power':ell,
      'radius':str(radius),'weight_cap':str(wc),'exponential_lower_integer_hex':hex(E),'num_pieces':len(leaves),
      'max_depth':max(d for d,i in leaves),'dyadic_pieces':leaves}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('witness',type=Path);p.add_argument('--weight-cap',default='51.70935');p.add_argument('--output',type=Path)
    a=p.parse_args();r=verify(a.witness,Q(a.weight_cap))
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k not in {'exponential_lower_integer_hex','dyadic_pieces'}},indent=2))
