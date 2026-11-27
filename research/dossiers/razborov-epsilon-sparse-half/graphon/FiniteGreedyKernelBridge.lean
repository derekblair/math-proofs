import FiniteGreedy
import FiniteKernelModel
import RestrictedAllocations

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [DecidableEq V]

lemma uniform_integral_finset (s : Finset V) (f : V→ℝ) :
    (∫ x in (s:Set V),f x ∂(uniformVertices : Measure V)) =
      (∑ x∈s,f x)/(Fintype.card V:ℝ) := by
  rw [← integral_indicator (s.finite_toSet.measurableSet),uniform_integral]
  congr 1
  simp only [Set.indicator,Set.piecewise,Finset.mem_coe,Pi.zero_apply]
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma uniform_K_deg_finite_set (W : Kernel V) (s : Finset V) (v : V) :
    deg ((uniformVertices : Measure V).restrict (s:Set V)) W v =
      (∑ x∈s,W.W (v,x))/(Fintype.card V:ℝ) :=
  uniform_integral_finset s _

lemma uniform_indicator_mass_finset (s : Finset V) :
    (∫ x, indicatorWeight (s:Set V) x ∂(uniformVertices : Measure V)) =
      (s.card:ℝ)/(Fintype.card V:ℝ) := by
  rw [indicatorWeight,integral_indicator s.finite_toSet.measurableSet,uniform_integral_finset]
  simp

/-- The analytic energy of a finite mark is its ordinary unordered
edge sum divided by the squared vertex count. -/
lemma uniform_mark_cost (W : Kernel V) (s : Finset V) :
    energyPair uniformVertices W (indicatorWeight (s:Set V)) (indicatorWeight (s:Set V))/2 =
      unorderedCost (fun x y=>W.W (x,y)) s/(Fintype.card V:ℝ)^2 := by
  let μ : Measure V := uniformVertices
  let a := indicatorWeight (s:Set V)
  have hm : Measurable a := measurable_const.indicator s.finite_toSet.measurableSet
  have ha₀ (x) : 0≤a x := by by_cases hx:x∈s <;> simp [a,indicatorWeight,hx]
  have ha₁ (x) : a x≤1 := by by_cases hx:x∈s <;> simp [a,indicatorWeight,hx]
  have hwr := reweight_energy μ W a a hm hm ha₀ ha₀ ha₁ ha₁
  change energyPair μ W a a/2 = _
  rw [← hwr,show reweight μ a = μ.restrict (s:Set V) from
    indicatorWeight_reweight μ (s:Set V) s.finite_toSet.measurableSet]
  rw [integral_prod W.W (integrable_bounded _ W.measurable_W W.nonneg W.le_one)]
  change (∫ x in (s:Set V), ∫ y in (s:Set V), W.W (x,y) ∂μ ∂μ)/2=_
  simp_rw [show μ = uniformVertices from rfl,uniform_integral_finset]
  unfold unorderedCost
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

#print axioms uniform_mark_cost
end SparseHalfGraphon
