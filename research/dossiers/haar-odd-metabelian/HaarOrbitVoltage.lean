import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

namespace HaarOrbitVoltage
variable {E B A : Type*} [Fintype E] [Fintype B] [DecidableEq B] [AddCommGroup A]

def value (c : E → ℤ) (w : E → A) : A := ∑ e, c e • w e

def flux (q : E → B) (c : E → ℤ) (b : B) : ℤ :=
  ∑ e, if q e = b then c e else 0

def Balanced (src dst : E → B) (c : E → ℤ) : Prop :=
  ∀ b, flux src c b = flux dst c b

theorem sum_via_vertices (f : E → B) (c : E → ℤ) (p : B → A) :
    (∑ e, c e • p (f e)) = ∑ b, flux f c b • p b := by
  classical
  unfold flux
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [ite_smul,zero_smul]
  simp

theorem combine_potential (src dst : E → B) (c : E → ℤ) (p : B → A)
    (bc : Balanced src dst c) :
    (∑ e, c e • p (src e)) = ∑ e, c e • p (dst e) := by
  rw [sum_via_vertices src c p,sum_via_vertices dst c p]
  apply Finset.sum_congr rfl
  intro b _
  rw [bc b]

/-- A deck conjugacy plus a vertex coboundary preserves vanishing voltage.
    The local voltage law is needed only on the chain's support. -/
theorem translated (src dst : E → B) (c : E → ℤ) (bc : Balanced src dst c)
    (w w' : E → A) (ψ : A →+ A) (p : B → A)
    (law : ∀ e, c e ≠ 0 → w' e = ψ (w e) + p (dst e) - p (src e)) :
    value c w' = ψ (value c w) := by
  unfold value
  rw [map_sum]
  calc
    _ = ∑ e, c e • (ψ (w e) + p (dst e) - p (src e)) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : c e=0
      · simp [h]
      · rw [law e h]
    _ = _ := by
      simp only [zsmul_sub,zsmul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,map_zsmul]
      rw [combine_potential src dst c p bc]
      abel

theorem translated_zero (src dst : E → B) (c : E → ℤ) (bc : Balanced src dst c)
    (w w' : E → A) (ψ : A →+ A) (p : B → A)
    (law : ∀ e, c e ≠ 0 → w' e = ψ (w e) + p (dst e) - p (src e))
    (h : value c w=0) : value c w'=0 := by
  rw [translated src dst c bc w w' ψ p law,h,map_zero]

end HaarOrbitVoltage
#print axioms HaarOrbitVoltage.translated_zero
