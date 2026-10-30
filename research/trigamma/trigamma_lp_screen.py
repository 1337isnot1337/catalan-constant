"""Exploratory continuum assignment LP for digamma frames; no proof certificate.

All pole sums are exact Fraction values. Geometric endpoints and LP use doubles.
LP is an upper bound for the local determinant-denominator cost through
assignment-dual potentials, before any nontrivial rank layer.
"""
import math,sys,json,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.integrate import simpson
from scipy.sparse import coo_matrix
from trigamma_screen import FRAMES,constants,pole_classes,local

def root_terms(shifts,weights,cls):
    from math import lcm
    q=lcm(*(s.denominator for s in shifts)); inv=pow(cls,-1,q)
    return [(F((int(s*q)*inv)%q or q,q),w) for s,w in zip(shifts,weights)]

def assignment(theta,alpha,terms):
    N=1+2*alpha
    cuts=sorted(set([0.,theta]+[float(k)*theta for k,w in terms]+[x-math.floor(x/theta)*theta for x in [1.,N]]))
    # Float near-boundary duplicates do not matter for zero-width intervals.
    rows=[];cols=[]; fibres=[]
    for a,b in zip(cuts,cuts[1:]):
        if b-a<1e-11:continue
        residue=(a+b)/2
        data=[]
        for k in range(max(0,math.ceil((N-residue)/theta))):
            t=residue+k*theta
            if t>=N-1e-10:continue
            L=F(0);E=F(0);has=False
            for kap,w in terms:
                count=k+int(residue>float(kap)*theta)
                if count:has=True
                for j in range(count):
                    L+=w/(j+kap);E+=w/(j+kap)**2
            data.append((k,t<1-1e-10,L,E,has))
        for parity in [0,1]:
            R=[];C=[]
            for k,common,L,E,has in data:
                d=dict(k=k,L=L,E=E,has=has,weight=(b-a)/2)
                if common or (parity+k)%2==0:
                    R.append(len(rows));rows.append(d)
                if common or (parity+k)%2==1:
                    C.append(len(cols));cols.append(d)
            fibres.append((R,C))
    nr,nc=len(rows),len(cols); bounds={}
    for i,r in enumerate(rows):
        for j,c in enumerate(cols):
            bounds[i,j]=int(r['L']!=c['L'])
    for R,C in fibres:
        for i in R:
            r=rows[i]
            for j in C:
                c=cols[j]
                if r['k']==c['k']:
                    v=2 if r['E'] else (1 if r['has'] else 0)
                else:
                    v=2 if r['L']!=c['L'] else (1 if r['has'] or c['has'] else 0)
                bounds[i,j]=max(bounds[i,j],v)
    # Variables are nonnegative potentials; omit trivial zero inequalities.
    data=[];ii=[];jj=[];rhs=[]
    for (i,j),v in bounds.items():
        if v:
            l=len(rhs); ii.extend([l,l]);jj.extend([i,nr+j]);data.extend([-1.,-1.]);rhs.append(-float(v))
    A=coo_matrix((data,(ii,jj)),shape=(len(rhs),nr+nc)).tocsr()
    cvec=[r['weight'] for r in rows]+[c['weight'] for c in cols]
    result=linprog(cvec,A_ub=A,b_ub=rhs,bounds=(0,2),method='highs')
    if not result.success:raise RuntimeError(result.message)
    return result.fun

def run(frame,name,ngrid=500):
    shifts,weights=FRAMES[frame];k=constants(name,len(shifts));alpha=k['Mq']-1
    cs=pole_classes(shifts,weights);details=[]
    for pc in cs:
        terms=root_terms(shifts,weights,pc['class_']);top=(1+2*alpha)/pc['ks'][0]
        xs=np.linspace(.05,top,ngrid+1);ys=[];old=[]
        for x in xs:
            base=local(x,alpha,pc);p=assignment(x,alpha,terms)
            ys.append(min(base,p));old.append(base)
        val=simpson(ys,x=xs)+.05*(2+2*alpha)
        details.append(dict(cls=pc['class_'],content=val,old=simpson(old,x=xs)+.05*(2+2*alpha),saving=simpson(np.array(old)-ys,x=xs)))
    lam=sum(d['content'] for d in details)/len(details);gap=k['Dnew']-lam
    res=dict(frame=frame,certificate=name,alpha=alpha,content=lam,decay=k['Dnew'],gap=gap,mu=k['ccert']/gap if gap>0 else None,details=details)
    print(json.dumps(res),flush=True)
    return res

if __name__=='__main__':
    start=time.time();res=[]
    if len(sys.argv)>1:
        res=[run(sys.argv[1],sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 500)]
    else:
        for frame in ['chi3_control','G_three','G_direct']:
            for name in ['Fourths','Chi3']:res.append(run(frame,name))
    (Path(__file__).parent/'trigamma_lp_results.json').write_text(json.dumps(res,indent=2))
    print('seconds',time.time()-start,flush=True)
