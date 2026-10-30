"""Exact scalar gates for a Catalan irrationality exponent of 531.55361.

The inputs NORM, FIELD, RESIDUAL and GAIN are inherited certified quantities.
The new gap and circle cap are certified by residual_certificate.py and the
separate circle certificate. This file checks their analytic assembly with
Fraction arithmetic, including every numerical condition of the criterion.
"""
import json
from fractions import Fraction as Q
from residual_certificate import LOG2, I

NORM=Q('0.7736205195')
FIELD=Q('-2.53949899')
RESIDUAL=Q('-0.0631062')
NEAR=Q('-0.77')
GAIN=Q(36235515874601938601596598,1642609663271115992578125)
U=Q('2.2558577253')
C2=Q('4.2881501')
WC=Q('52.6055')
W=Q('52.605501')
ETA=Q('30.0437525')
B=Q('531.55361')
DELTA=Q(1,10**10)
OMEGA=Q(3,4)

def verify():
    ell=LOG2
    margin=Q(41,58)*ell-NORM-FIELD-U
    slope=Q(76,29)*ell-FIELD+RESIDUAL-C2
    assert margin.lo>0
    assert slope.square().hi<=8*ell.lo*margin.lo
    assert (ell-RESIDUAL+NEAR).hi<0
    # The first-case certificate is reused unchanged; lowering U preserves it.
    assert U<Q('2.255858836')
    assert Q('4.09661')<C2
    assert W>WC
    rho=58*C2+W
    # 58^2(U-log(2)/2)-[(2673/8)log(2)+116+24269/4-GAIN].
    eta_bound=3364*U-Q(16129,8)*ell-Q(24733,4)+GAIN
    assert 0<ETA<eta_bound.lo
    kappa=B/rho
    assert 0<OMEGA<=1 and 2*OMEGA<kappa
    assert 0<ETA<106 and DELTA>0
    assert 1<2*(OMEGA-DELTA*(2*kappa-OMEGA))
    assert 53+4*53*DELTA*kappa<ETA*kappa
    threshold=53*rho/(ETA-4*53*DELTA)
    assert threshold<B
    result={
      'method':'exact rational arithmetic',
      'exponent':str(B),'rho':str(rho),'eta':str(ETA),'U':str(U),'c2':str(C2),
      'w':str(W),'gain':str(GAIN),'delta':str(DELTA),'omega':str(OMEGA),
      'margin_lower':str(margin.lo),
      'discriminant_margin_lower':str(8*ell.lo*margin.lo-slope.square().hi),
      'decay_margin_lower':str(eta_bound.lo-ETA),
      'criterion_threshold':str(threshold),'exponent_margin':str(B-threshold),
    }
    return result

if __name__=='__main__':
    result=verify();print(json.dumps(result,indent=2))
    print('display only: threshold =',float(Q(result['criterion_threshold'])))
