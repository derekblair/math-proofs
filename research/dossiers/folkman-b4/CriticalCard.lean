import CriticalKernel
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Field.Rat

namespace FolkmanB4.Critical
open Finset

theorem card_le_lines {L V : Type*} [Fintype L] [Fintype V]
    (I : L → V → Prop) (used : ∀ v, ∃ l, I l v)
    (bad : ¬∃ c, Good I univ c)
    (minimal : ∀ S : Finset L, S ≠ univ → ∃ c, Good I S c) :
    Fintype.card V ≤ Fintype.card L := by
  classical
  let A (l : L) (v : V) : ℚ := if I l v then 1 else 0
  let T : (V → ℚ) →ₗ[ℚ] (L → ℚ) :=
    { toFun := fun x l => ∑ v, A l v*x v
      map_add' := by
        intro x y
        funext l
        simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro t x
        funext l
        simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
        apply sum_congr rfl
        intro v _
        exact mul_left_comm _ _ _ }
  have ker : ∀ x : V → ℚ, T x=0 → x=0 := by
    intro x hx
    apply kernel_trivial I used bad minimal A
    · intro l v h; simp [A,h]
    · intro l v h; simp [A,h]
    · intro l
      exact congrFun hx l
  have inj : Function.Injective T := by
    intro a b h
    apply sub_eq_zero.mp
    apply ker
    rw [map_sub,h,sub_self]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective inj

#print axioms card_le_lines
end FolkmanB4.Critical
