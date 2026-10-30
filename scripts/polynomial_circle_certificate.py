"""Exact circle-norm certificate for the asymmetric degree-53 inverse image.

Let P be the rational degree-53 polynomial in the witness, Q(z)=P(z)(1-z)^6.
The squared modulus |Q(r exp(i theta))|^2 is a real Chebyshev polynomial in
cos(theta), obtained by exact autocorrelation. Rational Bernstein subdivision
bounds it on [-1,1]. Every branch decision is an integer/rational inequality.

The output proves |T_N(P(z))(1-z)^(6N)| <= exp(wc N) on |z|=r, for all N>=1.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without -O: certificate assertions are required.')

def exp_lower(x,terms=400):
    assert x>0 and terms>0
    s=t=Q(1)
    for k in range(1,terms):t*=x/k;s+=t
    return s

def chebyshev_to_power(cs):
    n=len(cs)-1;out=[0]*(n+1)
    tm=[1];t=[0,1]
    for k,c in enumerate(cs):
        tk=tm if k==0 else t
        for j,v in enumerate(tk):out[j]+=c*v
        if k>=1:
            nxt=[0]*(len(t)+1)
            for j,v in enumerate(t):nxt[j+1]+=2*v
            for j,v in enumerate(tm):nxt[j]-=v
            tm,t=t,nxt
    return out

def circle_squared_polynomial(cheb,radius,filter_degree=6):
    assert isinstance(filter_degree,int) and filter_degree>=0
    den=math.lcm(*(c.denominator for c in cheb))
    cint=[int(c*den) for c in cheb]
    power=chebyshev_to_power(cint)
    filt=[(-1)**j*math.comb(filter_degree,j) for j in range(filter_degree+1)]
    prod=[0]*(len(power)+filter_degree)
    for j,c in enumerate(power):
        for k,d in enumerate(filt):prod[j+k]+=c*d
    n=len(prod)-1;rn=radius.numerator;rd=radius.denominator
    scaled=[c*rn**j*rd**(n-j) for j,c in enumerate(prod)]
    modulus_den=den*rd**n
    ac=[sum(x*x for x in scaled)]
    for k in range(1,n+1):
        ac.append(2*sum(scaled[j]*scaled[j+k] for j in range(n-k+1)))
    return chebyshev_to_power(ac),modulus_den

def power_to_bernstein_on_minus_one_one(power):
    n=len(power)-1
    # Power coefficients after x=2t-1.
    p=[(1<<j)*sum(power[k]*math.comb(k,j)*(-1)**(k-j) for k in range(j,n+1)) for j in range(n+1)]
    b=[sum((Q(p[j]*math.comb(k,j),math.comb(n,j)) for j in range(k+1)),Q(0)) for k in range(n+1)]
    den=math.lcm(*(c.denominator for c in b))
    return [int(c*den) for c in b],den

def midpoint_split(b):
    """Integer numerators for both halves; common denominator multiplied by 2^n."""
    n=len(b)-1;row=b[:];left=[];right=[]
    for j in range(n+1):
        left.append(row[0]<<(n-j));right.append(row[-1]<<(n-j))
        row=[row[k]+row[k+1] for k in range(len(row)-1)]
    return left,list(reversed(right))

def verify(witness_path,weight_cap=Q('52.1049'),radius=Q(100000001,100000000),max_depth=40):
    raw=Path(witness_path).read_bytes();obj=json.loads(raw)
    cs=list(map(Q,obj['chebyshev_coefficients']))
    assert obj['degree']==53 and len(cs)==54 and cs[-1]!=0
    assert 1<radius<2 and weight_cap>0
    power,mden=circle_squared_polynomial(cs,radius)
    bern,bden=power_to_bernstein_on_minus_one_one(power)
    degree=len(bern)-1
    # 2 |Q(z)|+|1-z|^6 <= E, with E < exp(weight_cap).
    el=exp_lower(weight_cap);E=el.numerator//el.denominator
    H=(radius+1)**6
    assert E>H
    target=((Q(E)-H)/2)**2*mden*mden
    tn,td=target.numerator,target.denominator
    stack=[(bern,0,0)];leaves=[];deepest=0
    while stack:
        b,depth,index=stack.pop();den=bden<<(degree*depth)
        if max(b)*td<=tn*den:
            leaves.append([depth,index]);deepest=max(deepest,depth)
            continue
        assert depth<max_depth,('depth limit',depth,index)
        # A positive Bernstein lower bound beyond target disproves this cap.
        assert min(b)*td<=tn*den,('cap too small',depth,index)
        left,right=midpoint_split(b)
        stack.append((right,depth+1,index*2+1))
        stack.append((left,depth+1,index*2))
    # The recursive dyadic subdivision proves coverage; additionally audit it.
    endpoints=sorted((Q(index,1<<depth),Q(index+1,1<<depth)) for depth,index in leaves)
    cursor=Q(0)
    for a,b in endpoints:assert a==cursor and a<b;cursor=b
    assert cursor==1
    return {'format':'catalan-polynomial-circle-v1','method':'integer Bernstein subdivision of exact autocorrelation',
        'witness_sha256':hashlib.sha256(raw).hexdigest(),'degree':53,'squared_modulus_degree':degree,
        'radius':str(radius),'weight_cap':str(weight_cap),'E':str(E),'filter_cap':str(H),
        'num_pieces':len(leaves),'max_depth':deepest,'dyadic_pieces':leaves}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('witness',type=Path)
    p.add_argument('--weight-cap',default='52.1049')
    p.add_argument('--output',type=Path)
    args=p.parse_args();r=verify(args.witness,Q(args.weight_cap))
    if args.output:args.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k!='dyadic_pieces'},indent=2))
