import FiniteKernelModel
import StabilityLocal
open MeasureTheory Set
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfStability
variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [DecidableEq V] [LinearOrder V]

noncomputable def finiteHalf (s : V → ℝ)
    (ad : ∀ v, 0 ≤ s v ∧ s v ≤ 1/(Fintype.card V : ℝ))
    (m : ∑ v,s v = 1/2) (pos : 0 < Fintype.card V) :
    Half (uniformVertices : Measure V) where
  f v := (Fintype.card V : ℝ)*s v
  measurable_f := measurable_of_countable _
  nn v := mul_nonneg (Nat.cast_nonneg _) (ad v).1
  le_one v := by
    have p : 0 < (Fintype.card V : ℝ) := by exact_mod_cast pos
    have h := mul_le_mul_of_nonneg_left (ad v).2 p.le
    rwa [mul_one_div_cancel p.ne'] at h
  mass_half := by
    rw [uniform_integral,← Finset.mul_sum,m]
    have p : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
    field_simp

theorem half_energy_eq_edges (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (H : Half (uniformVertices : Measure V)) :
    halfEnergy uniformVertices (adjacencyKernel G sym) H =
      edgeCost G (fun v => H.f v/(Fintype.card V : ℝ)) := by
  rw [show edgeCost G (fun v => H.f v/(Fintype.card V : ℝ)) =
      orderedCost G (fun v => H.f v/(Fintype.card V : ℝ))/2 by
    rw [canonical_cost _ _ sym loop]
    ring] -- expose both expressions as one half of the directed sums
  unfold halfEnergy orderedCost
  simp_rw [uniform_integral]
  congr 1
  rw [div_eq_mul_inv,Finset.sum_mul,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  change edgeReal (G y x)*H.f y*(↑(Fintype.card V):ℝ)⁻¹*H.f x*(↑(Fintype.card V):ℝ)⁻¹ = _
  cases h : G y x <;> simp [edgeReal,h] <;> ring

theorem beta_le_of_finite_sparse (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (loop : ∀ v, G v v = false) (pos : 0 < Fintype.card V)
    (h : HasSparseFractional G) :
    beta uniformVertices (adjacencyKernel G sym) ≤ 1/50 := by
  obtain ⟨s,ad,m,cost⟩ := h
  let H := finiteHalf (V := V) s ad m pos
  have h₀ : beta uniformVertices (adjacencyKernel G sym) ≤
      halfEnergy uniformVertices (adjacencyKernel G sym) H :=
    csInf_le (range_bdd uniformVertices (adjacencyKernel G sym)) ⟨H,rfl⟩
  rw [half_energy_eq_edges G sym loop H] at h₀
  have eq : (fun v => H.f v/(Fintype.card V : ℝ)) = s := by
    funext v
    change (Fintype.card V : ℝ)*s v/(Fintype.card V : ℝ) = s v
    have h : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
    field_simp
  rw [eq] at h₀
  exact h₀.trans cost

#print axioms half_energy_eq_edges
#print axioms beta_le_of_finite_sparse
end SparseHalfGraphon
