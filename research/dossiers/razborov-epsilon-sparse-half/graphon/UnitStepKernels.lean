import UnitLabels
import FiberIntegrals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon
lemma kernel_extW {X : Type*} [MeasurableSpace X] {K J : Kernel X}
    (h : K.W = J.W) : K = J := by
  cases K
  cases J
  cases h
  rfl
end SparseHalfGraphon

namespace SparseHalfGraphon.CoherentTables

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable [∀ n, MeasurableSpace (I n)] [∀ n, MeasurableSingletonClass (I n)]
variable {p : ∀ n, I (n+1) → I n} (B : CoherentTables I p)

noncomputable def unitStep (n : ℕ) : Kernel UnitHalfOpen where
  W := fun z => B.density n (B.unitLabel n z.1) (B.unitLabel n z.2)
  measurable_W := (measurable_of_countable (fun z : I n × I n => B.density n z.1 z.2)).comp
    (pair_label_meas _ (B.unitLabel_meas n))
  nonneg := fun _ => B.density_nonneg n _ _
  le_one := fun _ => B.density_le_one n _ _
  symm := fun _ _ => B.density_symm n _ _

lemma rectangle_area (n : ℕ) (i j : I n) :
    (unitμ.prod unitμ).real (SparseHalfGraphon.cell (pairLabel (B.unitLabel n)) (i,j)) =
      B.cell n i * B.cell n j := by
  rw [pair_cell, measureReal_prod_prod, SparseHalfGraphon.cell, SparseHalfGraphon.cell, B.unitLabel_mass, B.unitLabel_mass]

lemma fine_integral (n : ℕ) (i j : I n) :
    (∫ z in SparseHalfGraphon.cell (pairLabel (B.unitLabel n)) (i,j), (B.unitStep (n+1)).W z ∂unitμ.prod unitμ) =
      B.joint n i j := by
  let c := pairLabel (B.unitLabel n)
  let d := pairLabel (B.unitLabel (n+1))
  let q : I (n+1) × I (n+1) → I n × I n := fun z => (p n z.1,p n z.2)
  have hq z : c z = q (d z) :=
    Prod.ext (B.unitLabel_parent n z.1).symm (B.unitLabel_parent n z.2).symm
  let v : I (n+1) × I (n+1) → ℝ := fun z => B.density (n+1) z.1 z.2
  change (∫ z in SparseHalfGraphon.cell c (i,j), v (d z) ∂unitμ.prod unitμ) = _
  rw [integral_parent_cell c d q (pair_label_meas _ (B.unitLabel_meas (n+1))) hq]
  have he (k : I (n+1) × I (n+1)) :
      (unitμ.prod unitμ).real (SparseHalfGraphon.cell d k) * v k = B.joint (n+1) k.1 k.2 := by
    rcases k with ⟨a,b⟩
    rw [show d = pairLabel (B.unitLabel (n+1)) from rfl, B.rectangle_area]
    exact (mul_comm _ _).trans (B.density_mul_area (n+1) a b)
  simp only [he]
  have hs :
      (Finset.univ.filter (fun k => q k = (i,j))) =
      (Finset.univ.filter (fun a => p n a = i)) ×ˢ
        (Finset.univ.filter (fun a => p n a = j)) := by
    ext k
    simp [q,Prod.ext_iff]
  rw [hs,Finset.sum_product]
  exact (B.joint_split n i j).symm

/-- Adjacent step kernels are linked by exact block averaging; this
repackages table conservation as an analytic conditional mean. -/
theorem unitStep_means (n : ℕ) :
    blockKernel unitμ (B.unitStep (n+1)) (B.unitLabel n) (B.unitLabel_meas n) =
      B.unitStep n := by
  apply kernel_extW
  funext z
  change (∫ y in SparseHalfGraphon.cell (pairLabel (B.unitLabel n))
      (B.unitLabel n z.1,B.unitLabel n z.2), (B.unitStep (n+1)).W y ∂unitμ.prod unitμ) /
      (unitμ.prod unitμ).real (SparseHalfGraphon.cell (pairLabel (B.unitLabel n))
      (B.unitLabel n z.1,B.unitLabel n z.2)) =
    B.density n (B.unitLabel n z.1) (B.unitLabel n z.2)
  rw [B.fine_integral, B.rectangle_area]
  rfl

#print axioms fine_integral
#print axioms unitStep_means
end SparseHalfGraphon.CoherentTables
