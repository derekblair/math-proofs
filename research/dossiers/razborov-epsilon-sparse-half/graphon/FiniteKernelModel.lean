import GraphonMantel
import HalfCutContinuity
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace SparseHalfGraphon

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Uniform probability measure on a nonempty finite vertex type.
Retaining the formula for the empty type gives the zero measure. -/
noncomputable def uniformVertices : Measure V :=
  ENNReal.ofReal (1/(Fintype.card V : ℝ)) • Measure.count

instance uniformVertices_finite : IsFiniteMeasure (uniformVertices : Measure V) := by
  unfold uniformVertices
  exact Measure.smul_finite Measure.count ENNReal.ofReal_ne_top

theorem uniform_singleton (v : V) :
    (uniformVertices : Measure V).real {v} = 1/(Fintype.card V : ℝ) := by
  simp [uniformVertices,ENNReal.toReal_ofReal,div_nonneg]

theorem uniform_integral (f : V → ℝ) :
    (∫ x, f x ∂(uniformVertices : Measure V)) = (∑ x, f x)/(Fintype.card V : ℝ) := by
  unfold uniformVertices
  rw [integral_smul_measure,integral_count,smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg zero_le_one (Nat.cast_nonneg _))]
  ring

theorem uniform_mass (h : 0 < Fintype.card V) : mass (uniformVertices : Measure V) = 1 := by
  have H := uniform_integral (fun _ : V => (1 : ℝ))
  simpa [mass,integral_const,smul_eq_mul,Finset.sum_const,div_self (by exact_mod_cast h.ne' :
    (Fintype.card V : ℝ) ≠ 0)] using H

theorem uniform_probability (h : 0 < Fintype.card V) :
    IsProbabilityMeasure (uniformVertices : Measure V) := by
  constructor
  have H := uniform_mass (V := V) h
  unfold mass Measure.real at H
  have eq := congrArg ENNReal.ofReal H
  simpa [ENNReal.ofReal_toReal (measure_ne_top _ _)] using eq

theorem uniform_finset (s : Finset V) :
    (uniformVertices : Measure V).real (s : Set V) = (s.card : ℝ)/(Fintype.card V : ℝ) := by
  unfold uniformVertices
  simp only [measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_ofReal (div_nonneg zero_le_one (Nat.cast_nonneg _))]
  unfold Measure.real
  rw [Measure.count_apply_finset,ENNReal.toReal_natCast]
  ring

def edgeReal (b : Bool) : ℝ := if b then 1 else 0

def adjacencyKernel (G : V → V → Bool) (sym : ∀ u v, G u v = G v u) : Kernel V where
  W := fun z => edgeReal (G z.1 z.2)
  measurable_W := measurable_of_countable _
  nonneg := fun z => by cases G z.1 z.2 <;> norm_num [edgeReal]
  le_one := fun z => by cases G z.1 z.2 <;> norm_num [edgeReal]
  symm := fun u v => congrArg edgeReal (sym u v)

theorem degree_finite (G : V → V → Bool) (sym : ∀ u v, G u v = G v u) (v : V) :
    deg uniformVertices (adjacencyKernel G sym) v =
      ((Finset.univ.filter (fun u => G v u = true)).card : ℝ)/(Fintype.card V : ℝ) := by
  unfold deg
  rw [uniform_integral]
  change (∑ u : V, if G v u = true then (1:ℝ) else 0)/(Fintype.card V : ℝ) = _
  simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

theorem adjacency_triangle_zero (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (h : ∀ u v w, G u v = true → G u w = true → G v w = false) :
    ∀ z, triangle (adjacencyKernel G sym) z = 0 := by
  rintro ⟨⟨u,v⟩,w⟩
  unfold triangle
  change edgeReal (G u v)*edgeReal (G u w)*edgeReal (G v w) = 0
  by_cases hv : G u v = true
  · by_cases hw : G u w = true
    · simp [edgeReal,hv,hw,h u v w hv hw]
    · simp [edgeReal,hv,hw]
  · simp [edgeReal,hv]

theorem adjacency_triangle_ae (G : V → V → Bool) (sym : ∀ u v, G u v = G v u)
    (h : ∀ u v w, G u v = true → G u w = true → G v w = false) :
    ∀ᵐ z ∂((uniformVertices : Measure V).prod uniformVertices).prod uniformVertices,
      triangle (adjacencyKernel G sym) z = 0 :=
  ae_of_all _ (adjacency_triangle_zero G sym h)

#print axioms uniform_probability
#print axioms degree_finite
#print axioms adjacency_triangle_ae
end SparseHalfGraphon
