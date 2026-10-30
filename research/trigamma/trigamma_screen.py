"""Exploratory arithmetic screen for new digamma frames. No certified bound.

Implements T1', pole-free-window W, and elementary regular-node potentials
from Litsey's paper-lambda, with arbitrary rational shifts and weights.
Numerical integration error and all analytical adaptations remain unproved.
"""
from fractions import Fraction as F
from math import floor, gcd
import argparse, json
from pathlib import Path
import numpy as np
from scipy.integrate import quad

def intersection(a,b,c,d):
    return max(0., min(b,d)-max(a,c))

def constants(name, new_d):
    """Read exact upstream scalars, then form an exploratory decay proxy."""
    data = json.loads((Path(__file__).parent / 'trigamma_inputs.json').read_text())
    record = data['certificates'][name]
    vals = {key: float(F(record[key])) for key in ['Mq', 'Scap', 'ccert', 'etaS', 'Dt']}
    vals['Dnew'] = vals['Dt'] + 2 * (new_d - record['dim']) * (vals['Scap'] - vals['etaS'])
    return vals

def pole_classes(shifts, weights):
    from math import lcm
    q=lcm(*(s.denominator for s in shifts))
    out=[]
    for u in range(q):
        if gcd(u,q)!=1: continue
        inv=pow(u,-1,q)
        ks=[F((int(s*q)*inv)%q or q,q) for s in shifts]
        ordered=sorted(zip(ks,weights))
        reg_border=[]; reg_common=[]; L=F(0);E=F(0);left=F(0)
        for right,w in ordered+[(F(1),F(0))]:
            if right>left and not L:
                reg_border.append((float(left),float(right)))
                if not E: reg_common.append((float(left),float(right)))
            if w:
                L+=w/right; E+=w/right**2
            left=right
        out.append(dict(class_=u,ks=sorted(set(float(k) for k in ks)),reg_common=reg_common,reg_border=reg_border))
    return out

def local(theta,alpha,pc):
    N=1+2*alpha; base=2+2*alpha
    # T1' assignment bound.
    rem=alpha%theta; gain=min(rem,theta-rem)
    # W, with prefix n=floor(alpha/theta).
    n=floor(alpha/theta+1e-12); Nn=N-2*n*theta
    low=max(1.,Nn-theta); high=min(Nn,1+theta)
    if high>low:
        cuts=[low,high]
        for shift in [0]+pc['ks']:
            j0=floor(low/theta-shift)-1;j1=floor(high/theta-shift)+1
            cuts.extend((j+shift)*theta for j in range(j0,j1+1) if low<(j+shift)*theta<high)
        cuts.extend(1+j*theta for j in range(-1,3) if low<1+j*theta<high)
        cuts.sort();gain=max(gain,max(b-a for a,b in zip(cuts,cuts[1:])))
    price=base-gain
    # No poles anywhere => all coefficients integral for this prime.
    if N<pc['ks'][0]*theta: return 0.
    # Regular nodes below first period; potentials valid when N<=2p.
    if N<=2*theta:
        saved=0.
        for a,b in pc['reg_common']:
            a*=theta;b*=theta
            saved+=intersection(a,b,max(0,1-theta),min(1,N-theta))
            saved+=2*intersection(a,b,max(0,N-theta),1)
        for a,b in pc['reg_border']:
            a*=theta;b*=theta
            saved+=intersection(a,b,max(1,N-theta),N)
        price=min(price,base-saved)
    return price

def screen(shifts,weights,alpha):
    cs=pole_classes(shifts,weights); out=[]
    for pc in cs:
        top=(1+2*alpha)/pc['ks'][0]
        # Resolve windows explicitly into fine quadrature bins.
        cuts=sorted(set([0.001,alpha,1+2*alpha,top]+list(np.linspace(.001,top,300))))
        val=.001*(2+2*alpha);err=0.
        for a,b in zip(cuts,cuts[1:]):
            if b<=a:continue
            v,e=quad(local,a,b,args=(alpha,pc),epsabs=2e-9,limit=100)
            val+=v;err+=e
        out.append(dict(**pc,content=val,quad_error=err))
    return sum(v['content'] for v in out)/len(out),out

FRAMES={
 'chi3_control':([F(1,3),F(1,2),F(1)],[-F(1,3),F(1,2),-F(1,6)]),
 'G_direct':([F(1,4),F(3,4)],[F(1),-F(1)]),
 'G_three':([F(1,4),F(1,2),F(1)],[-F(2),F(5),-F(3)]),
 'G_four':([F(1,4),F(3,4),F(1,2),F(1)],[F(5),-F(1),-F(10),F(6)]),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frame', choices=FRAMES, help='Omit to test every frame.')
    parser.add_argument('--certificate', choices=['Fourths', 'Fifths', 'Thirds', 'Chi3'])
    parser.add_argument('--output', type=Path, help='Optional JSON output path.')
    args = parser.parse_args()
    results = []
    for frame in ([args.frame] if args.frame else FRAMES):
        shifts, weights = FRAMES[frame]
        for name in ([args.certificate] if args.certificate else ['Fourths', 'Fifths', 'Thirds', 'Chi3']):
            k = constants(name, len(shifts))
            alpha = k['Mq'] - 1
            lam, detail = screen(shifts, weights, alpha)
            gap = k['Dnew'] - lam
            result = dict(frame=frame, certificate=name, alpha=alpha,
                          content=lam, decay=k['Dnew'], gamma=k['ccert'], gap=gap,
                          mu=k['ccert']/gap if gap>0 else None, details=detail)
            results.append(result)
            print(frame, name, 'Lambda', round(lam, 8), 'D', round(k['Dnew'], 8),
                  'gap', round(gap, 8), 'mu', result['mu'], flush=True)
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + '\n')
