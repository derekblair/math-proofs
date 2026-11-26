from pathlib import Path
from contextlib import redirect_stdout
from io import StringIO
with redirect_stdout(StringIO()):
 from extras_exact import GOOD,hit,W,base
S=[]
for p,a,b in GOOD:
 q=next(j for j in base if hit(p,a,b,*W[j]))
 S.append((p,a,b,base.index(q)))
pre='''import RibbonAllOddCore
import RibbonAffineModCore

namespace RibbonAllOddField
open RibbonAffine (eRow)
variable {K : Type*} [Field K]

def separates (a b : Kˣ) (k : Count) : Prop :=
  ∀ i j : Fin 64, i.val<j.val →
    eRow a b (symbol k i.val)=eRow a b (symbol k j.val) → IsMate (spec k) i.val j.val
instance {p : Nat} [Fact (Nat.Prime p)] (a b : (ZMod p)ˣ) (k : Count) :
    Decidable (separates a b k) := by unfold separates; infer_instance

private theorem transfer (p x y : Nat) [hp : Fact (Nat.Prime p)]
    (a b : Kˣ) (z : (p:K)=0) (A : (a:K)=(x:K)) (B : (b:K)=(y:K))
    (hx : (x:ZMod p)≠0) (hy : (y:ZMod p)≠0) (k : Count)
    (S : separates (Units.mk0 (x:ZMod p) hx) (Units.mk0 (y:ZMod p) hy) k) :
    separates a b k := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) hp.out).mpr z
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  have X : Units.map f.toMonoidHom (Units.mk0 (x:ZMod p) hx)=a := by
    apply Units.ext
    change f (x:ZMod p)=(a:K)
    rw [map_natCast,A]
  have Y : Units.map f.toMonoidHom (Units.mk0 (y:ZMod p) hy)=b := by
    apply Units.ext
    change f (y:ZMod p)=(b:K)
    rw [map_natCast,B]
  intro i j lt E
  apply S i j lt
  apply RibbonAffine.map_eRow_inj f
  rwa [X,Y]

set_option maxHeartbeats 0
set_option maxRecDepth 20000
'''
for p in (11,13,43):pre+=f'local instance prime{p} : Fact (Nat.Prime {p}) := ⟨by decide⟩\n'
pre+='def extraCases : Fin 13 → Nat × Nat × Nat × Count := !['+','.join(str(row).replace(' ','') for row in S)+']\n'
for i,(p,a,b,k) in enumerate(S):
 pre+=f'''
private theorem extra{i} : separates (Units.mk0 (({a}:Nat):ZMod {p}) (by decide))
    (Units.mk0 (({b}:Nat):ZMod {p}) (by decide)) {k} := by decide +kernel
'''
pre+='''
theorem extra_separates (a b : Kˣ) (i : Fin 13)
    (P : (((extraCases i).1:Nat):K)=0)
    (A : (a:K)=(((extraCases i).2.1:Nat):K))
    (B : (b:K)=(((extraCases i).2.2.1:Nat):K)) : separates a b (extraCases i).2.2.2 := by
  fin_cases i
'''
for i,(p,a,b,k) in enumerate(S):pre+=f'  · exact transfer {p} {a} {b} a b P A B (by decide) (by decide) {k} extra{i}\n'
pre+='\nend RibbonAllOddField\n#print axioms RibbonAllOddField.extra_separates\n'
Path('RibbonAllOddExtras.lean').write_text(pre)
