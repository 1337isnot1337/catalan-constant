"""Generate trimmed residual witnesses for the upstream Lean CellCert engine.

The Python calculations select witnesses only. Every generated value enclosure,
derivative list, pole bound, Taylor bound and cover is checked by `decide +kernel`
in Lean and linked to the residual field by upstream soundness theorems.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import argparse,json,re
from residual_certificate import parse_trial
from fast_rational_fields import derivative_poly,value

ROOT=Path(__file__).resolve().parents[1]
TT=1<<40
SC=1<<128
CAP=Q(-883,10000)
M=5
L=4
LT=65

def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
def cd(a,b):return (a+b-1)//b
def qtext(q):
    q=Q(q)
    return str(q.numerator) if q.denominator==1 else f'{q.numerator}/{q.denominator}'
def zs(a):return '['+', '.join(map(str,a))+']'
def cmul(x,y):return x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]

class Generator:
    def __init__(self,trial_path,source_root):
        self.cs,self.tails=parse_trial(trial_path)
        text=(source_root/'CatalanMeasure/GenD/D58/Cert590/RTab.lean').read_text()
        self.mgl=int(re.search(r'def MGL_R : ℤ := ([0-9]+)',text).group(1))
        self.poles=[(Q(-106,58),Q(0),Q(0),Q(1))]
        for zr,zi,rr,ri in self.tails:
            z2=zr*zr+zi*zi
            self.poles.append((rr,ri,zr*(1+z2)/(2*z2),zi*(z2-1)/(2*z2)))
        self.cache={}
    def poly(self,cc):
        return derivative_poly(Q(cc,TT),self.cs)
    def pb(self,poly,hh,m,length,top):
        # Exact mirror of PbV: polynomial entries are physical derivatives.
        out=0
        for k in range(length):
            j=m+k;a=abs(floor(SC*poly[j]*factorial(j)))+1
            out+=cd(a*hh**k,TT**k*factorial(k))
        return out+cd(top*hh**length,TT**length*factorial(length))
    def cell(self,lo,hi,bb):
        assert (lo+hi)%2==0 and lo<hi
        cc=(lo+hi)//2;hh=(hi-lo)//2;c=Q(cc,TT)
        if cc not in self.cache:
            poly=self.poly(cc)
            # The allowance exceeds the adaptive WLog enclosure error; Lean
            # checks the actual upper bound, so this allowance is untrusted.
            u=Q(ceil((value(c,self.cs,self.tails).hi+Q(1,10**8))*2**64),2**64)
            fh=[floor(SC*poly[j]*factorial(j)) for j in range(M)]
            for rr,ri,pr,pi in self.poles:
                ar=c-pr;ai=-pi;den=ar*ar+ai*ai
                inv=(ar/den,-ai/den);power=(Q(1),Q(0))
                for j in range(M):
                    power=cmul(power,inv)
                    f=(-1)**j*factorial(j)*(rr*power[0]-ri*power[1])
                    fh[j]+=floor(SC*f)
            aa=[abs(floor(SC*poly[M+k]*factorial(M+k)))+1 for k in range(L)]
            self.cache[cc]=u,fh,aa
        u,fh,aa=self.cache[cc]
        mp=0
        for rr,ri,pr,pi in self.poles:
            dl=max(Q(0),Q(lo,TT)-pr,pr-Q(hi,TT),abs(pi))
            assert dl>0
            mp+=ceil(SC*(abs(rr)+abs(ri))*factorial(M)/dl**(M+1))
        bsum=sum(cd((abs(fh[j])+1+len(self.poles))*hh**(j+1),TT**(j+1)*factorial(j+1)) for j in range(M))
        pb=sum(cd(aa[k]*hh**k,TT**k*factorial(k)) for k in range(L))+cd(bb*hh**L,TT**L*factorial(L))
        check=ceil(SC*u)+bsum+cd((mp+pb)*hh**(M+1),TT**(M+1)*factorial(M+1))
        return {'cc':cc,'hh':hh,'u':str(u),'fh':fh,'aa':aa,'mp':mp,'check':check,'passes':check<=floor(SC*CAP)}
    def block(self,lo,hi,index):
        assert (lo+hi)%2==0
        cc=(lo+hi)//2;hh=(hi-lo)//2
        bb=self.pb(self.poly(cc),hh,M+L,LT-L,self.mgl)
        cells=[];stack=[(lo,hi)]
        while stack:
            a,b=stack.pop();cell=self.cell(a,b,bb)
            if cell['passes']:cells.append(cell)
            else:
                assert b-a>2,('Cannot refine dyadic cell',a,b,cell)
                mid=(a+b)//2
                if (mid-a)%2:ml,mr=mid+1,mid-1
                else:ml=mr=mid
                assert ml<b and a<mr
                stack.append((mr,b));stack.append((a,ml))
        print('block',index,'cells',len(cells),flush=True)
        return {'index':index,'lo':lo,'hi':hi,'cc':cc,'hh':hh,'bb':bb,'cells':cells}

def emit_block(block,out):
    i=block['index'];n=f'trimmedRB{i:03d}';bb=block['bb'];cB=block['cc'];hB=block['hh']
    cells=block['cells'];ct='['+', '.join(f'(({c["cc"]}:ℤ),({c["hh"]}:ℤ),0)' for c in cells)+']'
    s=f'''module
public import Submission.Improvement.Fields.ResidualCommon
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def {n} : Block := ⟨{cB}, {hB}, {L}, {bb}, {ct}⟩
theorem {n}_blk : decide (PbV D_R.N {n}.cB {n}.HB
    (polyValsS D_R {n}.cB ({M}+{LT})) ({M}+{n}.L) ({LT}-{n}.L) MGL_R ≤ {n}.BB) = true := by decide +kernel
'''
    for j,c in enumerate(cells):
        tag=f'{n}_c{j}';cc=c['cc'];hh=c['hh'];u=qtext(Q(c['u']));fh=zs(c['fh']);aa=zs(c['aa']);mp=c['mp']
        s+=f'''theorem {tag}_ev : evLe (resSpecW (53/58:ℚ) Pc P 0).ev
    (({cc}:ℚ)/(TT:ℚ)) ({u}:ℚ) = true := by decide +kernel
theorem {tag}_fh : fhL D_R.N (resSpecW (53/58:ℚ) Pc P 0).poles ({cc}:ℤ)
    (polyValsS D_R ({cc}:ℤ) ({M}+{L})) {M} = {fh} := by decide +kernel
theorem {tag}_aa : AL D_R.N (polyValsS D_R ({cc}:ℤ) ({M}+{L})) {M} {L} = {aa} := by decide +kernel
theorem {tag}_mp : MpoleV (resSpecW (53/58:ℚ) Pc P 0).poles {M}
    (((({cc}:ℤ)-({hh}:ℤ):ℤ):ℚ)/(TT:ℚ))
    (((( {cc}:ℤ)+({hh}:ℤ):ℤ):ℚ)/(TT:ℚ)) = {mp} := by decide +kernel
theorem {tag}_fin : cellFin D_R.toD (resSpecW (53/58:ℚ) Pc P 0).poles
    {M} {L} {bb} none trimmedResidualCap ({cc},{hh}) ({u}:ℚ) {fh} {aa} {mp} = true := by decide +kernel
'''
    s+=f'''theorem {n}_cells : ∀ c ∈ {n}.cells,
    |c.1 - {n}.cB| + c.2.1 ≤ {n}.HB ∧
    cellT (resSpecW (53/58:ℚ) Pc P) D_R.toD {M} {n}.L {n}.BB trimmedResidualCap c = true := by
  intro c hc
  simp only [{n}, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with '''+' | '.join('rfl' for _ in cells)+'\n'
    for j,c in enumerate(cells):
        tag=f'{n}_c{j}'
        s+=f'''  · exact ⟨by decide +kernel,
      cellT_none_of_piecesS (resSpecW (53/58:ℚ) Pc P) D_R {M} {L} {bb}
        trimmedResidualCap ({c['cc']}:ℤ) ({c['hh']}:ℤ) 0 _ _ _ _ rfl
        {tag}_ev {tag}_fh {tag}_aa {tag}_mp {tag}_fin⟩
'''
    s+=f'''theorem {n}_ok : blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD
    {M} {LT} MGL_R trimmedResidualCap {n} = true :=
  blockOK_ofS (resSpecW (53/58:ℚ) Pc P) D_R {M} {LT} MGL_R trimmedResidualCap {n}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) {n}_blk {n}_cells
end CatalanMeasure.Improvement.Fields
'''
    (out/f'ResidualBlock{i:03d}.lean').write_text(s)

def emit_cover(blocks,groups,support,out):
    s='module\n\n'
    for b in blocks:s+=f'public import Submission.Improvement.Fields.ResidualBlock{b["index"]:03d}\n'
    s+='''
@[expose] public section
namespace CatalanMeasure.Improvement.Fields
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan Set
open CatalanMeasure.GenD.D58.Cert590
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
'''
    for side,indices,(lo,hi) in zip(['Left','Right'],groups,support):
        name='trimmedBlocks'+side
        s+=f'def {name} : List Block := ['+', '.join(f'trimmedRB{i:03d}' for i in indices)+']\n'
        s+=f'''theorem {name}_ok : ∀ b ∈ {name},
    blockOK (resSpecW (53/58:ℚ) Pc P) D_R.toD 5 65 MGL_R trimmedResidualCap b = true := by
  intro b hb
  simp only [{name}, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with '''+' | '.join('rfl' for _ in indices)+'\n'
        for i in indices:s+=f'  · exact trimmedRB{i:03d}_ok\n'
        start=blocks[indices[0]]['lo']
        s+=f'''theorem {name}_cover : coverFrom ({qtext(hi)}) ({start}) (blocksCells {name}) = true := by
  decide +kernel
theorem trimmed_residual_{side.lower()} (x : ℝ)
    (hxlo : ({qtext(lo)}:ℝ) ≤ x) (hxhi : x ≤ ({qtext(hi)}:ℝ)) :
    resFieldW ((53/58:ℚ):ℝ) (trialSeqS Pc P) x ≤ (trimmedResidualCap:ℝ) := by
  refine field_le_of_blocks _ (resSpecW (53/58:ℚ) Pc P) D_R.toD D_R_ok
    5 65 MGL_R hMGL_R trimmedResidualCap {name}
    (fun c _ => trimmed_residual_spec_sound c.2.2) ({start}) ({qtext(hi)})
    {name}_cover {name}_ok x ?_ ?_ ?_
  · have hlo : (({start}:ℤ):ℝ) / TT ≤ ({qtext(lo)}:ℝ) := by norm_num [TT]
    exact hlo.trans hxlo
  · exact_mod_cast hxhi
  · intro c hc pr hp
    simp [resSpecW] at hp
'''
    s+='''
theorem residual_sup_trimmed_W (x : ℝ) (hx : trimmedResidualSupport x) :
    resFieldW ((53/58:ℚ):ℝ) (trialSeqS Pc P) x ≤ (trimmedResidualCap:ℝ) := by
  rcases hx with h | h
  · exact trimmed_residual_left x h.1 h.2
  · exact trimmed_residual_right x h.1 h.2

theorem residual_sup_trimmed (x : ℝ) (hx : trimmedResidualSupport x) :
    GenD.Analytic.resFieldGen (GenD.Analytic.gRes GenD.D58.Odd.design)
      (trialSeqS Pc P) x ≤ (-883/10000:ℝ) := by
  have h := residual_sup_trimmed_W x hx
  norm_num [resFieldW, GenD.Analytic.resFieldGen, GenD.Analytic.gRes,
    GenD.D58.Odd.design, trimmedResidualCap] at h ⊢
  exact h

end CatalanMeasure.Improvement.Fields

#print axioms CatalanMeasure.Improvement.Fields.residual_sup_trimmed
'''
    (out/'ResidualTrimmed.lean').write_text(s)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'Submission/Improvement/Fields')
    parser.add_argument('--witness',type=Path,default=ROOT/'certificates/residual_lean_witness.json')
    parser.add_argument('--from-witness',action='store_true',
        help='Emit Lean from the saved rational witness without repeating witness selection.')
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    if args.from_witness:
        data=json.loads(args.witness.read_text())
        assert Q(data['cap'])==CAP
        support=[tuple(map(Q,p)) for p in data['support']]
        for block in data['blocks']:emit_block(block,args.output)
        emit_cover(data['blocks'],data['groups'],support,args.output)
        print('emitted',len(data['blocks']),'blocks from',args.witness)
        return
    gen=Generator(ROOT/'certificates/trial_data.json',ROOT/'Submission')
    support=[(Q(-2409,2500),Q(-19501,100000)),(Q(98749,1000000),Q(1))]
    blocks=[];groups=[]
    for lo,hi in support:
        a=2*floor(lo*TT/2);b=2*ceil(hi*TT/2)
        points=[a]+list(range((a//(TT//32)+1)*(TT//32),b,TT//32))+[b]
        group=[]
        for x,y in zip(points,points[1:]):
            block=gen.block(x,y,len(blocks));group.append(block['index']);blocks.append(block)
            emit_block(block,args.output)
        groups.append(group)
    args.witness.write_text(json.dumps({'cap':str(CAP),'support':[[str(x),str(y)] for x,y in support],
        'groups':groups,'blocks':blocks},indent=2)+'\n')
    emit_cover(blocks,groups,support,args.output)
    print('generated',len(blocks),'blocks',sum(len(b['cells']) for b in blocks),'cells')

if __name__=='__main__':main()
