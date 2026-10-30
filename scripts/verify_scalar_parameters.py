"""Verify rational scalar data for the unchanged design and arithmetic profile.

The supplied residual and near-field caps must be proved separately for the
quadrature support. This verifies their assembly and the numerical criterion.
"""
import argparse,json
from fractions import Fraction as Q
from pathlib import Path
from scalar_certificate import NORM,FIELD,GAIN
from residual_certificate import LOG2

def verify(data):
    U,C2,WC,W,ETA,B,R,NEAR,DELTA,OMEGA=(Q(data[k]) for k in ['U','c2','weight_cap','w','eta','exponent','residual_cap','near_cap','delta','omega'])
    ell=LOG2;m=Q(41,58)*ell-NORM-FIELD-U;s=Q(76,29)*ell-FIELD+R-C2
    assert m.lo>0 and s.square().hi<8*ell.lo*m.lo
    assert (ell-R+NEAR).hi<0
    assert U<Q('2.255858836') and Q('4.09661')<C2 and W>WC
    rho=58*C2+W
    actual_eta=3364*U-Q(16129,8)*ell-Q(24733,4)+GAIN
    assert 0<ETA<actual_eta.lo
    kappa=B/rho
    assert 0<OMEGA<=1 and 2*OMEGA<kappa and ETA<106 and DELTA>0
    assert 1<2*(OMEGA-DELTA*(2*kappa-OMEGA))
    assert 53+212*DELTA*kappa<ETA*kappa
    threshold=53*rho/(ETA-212*DELTA);assert threshold<B
    return {'method':'exact rational arithmetic',**data,'rho':str(rho),'gain':str(GAIN),
        'budget_margin_lower':str(m.lo),'discriminant_margin_lower':str(8*ell.lo*m.lo-s.square().hi),
        'decay_margin_lower':str(actual_eta.lo-ETA),'criterion_threshold':str(threshold),
        'exponent_margin':str(B-threshold)}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('parameters',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();r=verify(json.loads(a.parameters.read_text()))
    if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2));print('display only: threshold =',float(Q(r['criterion_threshold'])))
