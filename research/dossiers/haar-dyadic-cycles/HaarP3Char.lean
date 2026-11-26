import HaarP3LayerGenConcrete
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace HaarP3Char
open HaarClass4Structure HaarP3LayerGen
variable {G : Type*} [Group G]

abbrev C3 := Multiplicative (ZMod 3)

theorem exists_separating {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (cube : ∀ w∈S, w^(3:ℕ)=1) (z : S) (ne : z≠1) :
    ∃ χ : S →* C3, χ z ≠ 1 := by
  let : CommGroup S :=
    { toGroup := inferInstance
      mul_comm := fun a b =>
        Subtype.ext ((Subgroup.mem_center_iff.mp (central a.property) b.val).symm) }
  let V := Additive S
  let : Module (ZMod 3) V := AddCommGroup.zmodModule (by
    intro u
    change Additive.toMul u ^ (3:ℕ) = 1
    exact Subtype.ext (cube _ (Additive.toMul u).property))
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have z0 : (Additive.ofMul z : V) ≠ 0 := ne
  obtain ⟨F,hF⟩ := Module.Projective.exists_dual_ne_zero (ZMod 3) z0
  let χ : S →* C3 :=
    { toFun := fun w => Multiplicative.ofAdd (F (Additive.ofMul w))
      map_one' := by change Multiplicative.ofAdd (F 0) = _; rw [map_zero]; rfl
      map_mul' := by
        intro a b
        change Multiplicative.ofAdd (F (Additive.ofMul a+Additive.ofMul b)) =
          Multiplicative.ofAdd (F (Additive.ofMul a)) * Multiplicative.ofAdd (F (Additive.ofMul b))
        rw [map_add]; rfl }
  exact ⟨χ,hF⟩

theorem separated_equal {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (cube : ∀ w∈S, w^(3:ℕ)=1) (a b : S)
    (he : ∀ χ : S →* C3, χ ≠ 1 → χ a = χ b) : a=b := by
  by_contra hn
  have h1 : a*b⁻¹≠1 := by
    intro e
    apply hn
    calc
      a = a*b⁻¹*b := by group
      _ = b := by rw [e,one_mul]
  obtain ⟨χ,hχ⟩ := exists_separating central cube (a*b⁻¹) h1
  have nχ : χ≠1 := by
    intro e
    exact hχ (by rw [e]; rfl)
  have h := he χ nχ
  exact hχ (by rw [map_mul,map_inv,h,mul_inv_cancel])

end HaarP3Char

#print axioms HaarP3Char.exists_separating
#print axioms HaarP3Char.separated_equal
