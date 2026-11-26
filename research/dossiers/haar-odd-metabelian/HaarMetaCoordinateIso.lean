import HaarMetaAlgebraCore
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fintype.EquivFin

namespace HaarMetaCoordinateIso

variable {Q : Type*} [Group Q]

noncomputable def orient (z : Q) (gen : Subgroup.zpowers z=⊤) (m : ℕ)
    (card : Nat.card Q=m) : Q ≃* Multiplicative (ZMod m) :=
  (zmodMulEquivOfGenerator (fun q => gen.symm ▸ Subgroup.mem_top q) card).symm

theorem orient_zpow (z : Q) (gen : Subgroup.zpowers z=⊤) (m : ℕ)
    (card : Nat.card Q=m) (i : ℤ) :
    orient z gen m card (z^i)=Multiplicative.ofAdd (i : ZMod m) :=
  zmodMulEquivOfGenerator_symm_apply_zpow _ _ i

end HaarMetaCoordinateIso
#print axioms HaarMetaCoordinateIso.orient_zpow
