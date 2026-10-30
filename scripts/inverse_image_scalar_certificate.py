"""Exact scalar assembly for the degree-53 asymmetric inverse-image polynomial."""
import json
from fractions import Fraction as Q
from scalar_certificate import NORM,FIELD,RESIDUAL,NEAR,GAIN,DELTA,OMEGA
from residual_certificate import LOG2

U=Q('2.2558577117')
C2=Q('4.28814215')
WC=Q('52.1049')
W=Q('52.104901')
ETA=Q('30.0437067')
B=Q('530.6705')

def verify():
    ell=LOG2
    m=Q(41,58)*ell-NORM-FIELD-U
    s=Q(76,29)*ell-FIELD+RESIDUAL-C2
    assert m.lo>0 and s.square().hi<8*ell.lo*m.lo
    assert (ell-RESIDUAL+NEAR).hi<0
    assert U<Q('2.255858836') and Q('4.09661')<C2
    assert W>WC
    rho=58*C2+W
    actual_eta=3364*U-Q(16129,8)*ell-Q(24733,4)+GAIN
    assert 0<ETA<actual_eta.lo
    kappa=B/rho
    assert 0<OMEGA<=1 and 2*OMEGA<kappa and ETA<106 and DELTA>0
    assert 1<2*(OMEGA-DELTA*(2*kappa-OMEGA))
    assert 53+212*DELTA*kappa<ETA*kappa
    threshold=53*rho/(ETA-212*DELTA)
    assert threshold<B
    return {'method':'exact rational arithmetic','exponent':str(B),'rho':str(rho),'eta':str(ETA),
        'U':str(U),'c2':str(C2),'w':str(W),'weight_cap':str(WC),'gain':str(GAIN),
        'delta':str(DELTA),'omega':str(OMEGA),'budget_margin_lower':str(m.lo),
        'discriminant_margin_lower':str(8*ell.lo*m.lo-s.square().hi),
        'decay_margin_lower':str(actual_eta.lo-ETA),'criterion_threshold':str(threshold),
        'exponent_margin':str(B-threshold)}

if __name__=='__main__':
    r=verify();print(json.dumps(r,indent=2))
    print('display only: threshold =',float(Q(r['criterion_threshold'])))
