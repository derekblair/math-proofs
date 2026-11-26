import RibbonStationaryBaseData
import RibbonAffineModCore

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (eRow)
variable {K : Type*} [Field K]
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def separates (a b : Kˣ) (k : Count) : Prop :=
  ∀ i j : Fin 64, i.val<j.val →
    eRow a b (symbol k i.val)=eRow a b (symbol k j.val) → IsMate (spec k) i.val j.val
instance (a b : (ZMod 11)ˣ) (k : Count) : Decidable (separates a b k) := by unfold separates; infer_instance

def extra : Fin 8 → (ZMod 11)ˣ × (ZMod 11)ˣ × Count :=
  ![(Units.mk0 (3 : ZMod 11) (by decide),Units.mk0 (5 : ZMod 11) (by decide),13),
    (Units.mk0 (3 : ZMod 11) (by decide),Units.mk0 (9 : ZMod 11) (by decide),11),
    (Units.mk0 (4 : ZMod 11) (by decide),Units.mk0 (5 : ZMod 11) (by decide),12),
    (Units.mk0 (4 : ZMod 11) (by decide),Units.mk0 (9 : ZMod 11) (by decide),9),
    (Units.mk0 (5 : ZMod 11) (by decide),Units.mk0 (3 : ZMod 11) (by decide),17),
    (Units.mk0 (5 : ZMod 11) (by decide),Units.mk0 (4 : ZMod 11) (by decide),14),
    (Units.mk0 (9 : ZMod 11) (by decide),Units.mk0 (3 : ZMod 11) (by decide),16),
    (Units.mk0 (9 : ZMod 11) (by decide),Units.mk0 (4 : ZMod 11) (by decide),15)]

set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem extra_valid : ∀ k : Fin 8, separates (extra k).1 (extra k).2.1 (extra k).2.2 := by decide +kernel

theorem extra_separates (a b : Kˣ) (p : (11:K)=0) (k : Fin 8)
    (A : (a:K)=(((extra k).1.val.val):K)) (B : (b:K)=(((extra k).2.1.val.val):K)) :
    separates a b (extra k).2.2 := by
  letI : CharP K 11 := (CharP.charP_iff_prime_eq_zero (R:=K) (by decide : Nat.Prime 11)).mpr p
  let f : ZMod 11→+*K := ZMod.castHom (dvd_refl 11) K
  have fA : Units.map f.toMonoidHom (extra k).1 = a := by
    apply Units.ext
    change f (extra k).1.val=(a:K)
    rw [←ZMod.natCast_zmod_val (extra k).1.val,map_natCast,A]
  have fB : Units.map f.toMonoidHom (extra k).2.1 = b := by
    apply Units.ext
    change f (extra k).2.1.val=(b:K)
    rw [←ZMod.natCast_zmod_val (extra k).2.1.val,map_natCast,B]
  intro i j lt E
  apply extra_valid k i j lt
  apply RibbonAffine.map_eRow_inj f
  rwa [fA,fB]

end RibbonStationaryField
#print axioms RibbonStationaryField.extra_separates
