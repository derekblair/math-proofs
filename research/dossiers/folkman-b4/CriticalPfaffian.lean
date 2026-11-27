import DetMatching
import CriticalCubic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace FolkmanB4.Critical
open Matrix Finset

theorem square_has_constant_sign {V : Type*} [Fintype V] [DecidableEq V]
    (I : V → V → Prop) [DecidableRel I]
    (used : ∀ v, ∃ l, I l v) (bad : ¬∃ c, Good I univ c)
    (minimal : ∀ S : Finset V, S≠univ → ∃ c, Good I S c)
    {s t : Equiv.Perm V} (hs : supported I s) (ht : supported I t) :
    pSign s=pSign t := by
  apply same_matching_sign I ?_ hs ht
  intro A P
  have ker : ∀ x : V → ℚ, A*ᵥx=0 → x=0 := by
    intro x h
    apply kernel_trivial I used bad minimal A P.1 P.2 x
    intro l
    exact congrFun h l
  have inj : Function.Injective A.mulVec := by
    intro a b h
    apply sub_eq_zero.mp
    apply ker
    rw [mulVec_sub,h,sub_self]
  exact ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp inj)).ne_zero

#print axioms square_has_constant_sign
end FolkmanB4.Critical
