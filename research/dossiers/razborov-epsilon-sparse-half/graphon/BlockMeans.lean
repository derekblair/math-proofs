import GraphonCaseTwoMarginals

open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def cell (c : X→ι) (i : ι) : Set X := c ⁻¹' {i}

noncomputable def meanCell (c : X→ι) (f : X→ℝ) (i : ι) : ℝ :=
  (∫ x in cell c i, f x ∂μ)/(μ.real (cell c i))

noncomputable def meanBlock (c : X→ι) (f : X→ℝ) (x : X) : ℝ :=
  meanCell μ c f (c x)

lemma bmeas_comp_finite (c : X→ι) (hc : Measurable c) (g : ι→ℝ) :
    BMeas (g ∘ c) := by
  classical
  exact ⟨(measurable_of_countable g).comp hc,∑ i, |g i|, fun x =>
    Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ (c x))⟩

lemma block_bmeas (c : X→ι) (hc : Measurable c) (f : X→ℝ) :
    BMeas (meanBlock μ c f) :=
  bmeas_comp_finite c hc (meanCell μ c f)

lemma mean_cell_exact (c : X→ι) (i : ι) (f : X→ℝ) :
    μ.real (cell c i)*meanCell μ c f i=∫ x in cell c i, f x ∂μ := by
  unfold meanCell
  by_cases hh : μ.real (cell c i)=0
  · have hz : μ (cell c i)=0 := (measureReal_eq_zero_iff).mp hh
    simp only [hh,zero_mul,Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
  · field_simp

/-- Mean residual on every cell is exactly zero, including empty/null cells. -/
lemma mean_zero (c : X→ι) (hc : Measurable c) (f : X→ℝ) (hf : BMeas f) (i : ι) :
    (∫ x in cell c i, f x-meanCell μ c f i ∂μ)=0 := by
  have hi := (bMeas_integrable μ hf).integrableOn (s:=cell c i)
  rw [integral_sub (μ:=μ.restrict (cell c i)) hi (integrable_const _),setIntegral_const,smul_eq_mul,
    mean_cell_exact μ c i f]
  ring

/-- Orthogonality of a residual to any cell-constant test function. -/
theorem mean_orthogonal (c : X→ι) (hc : Measurable c) (f : X→ℝ)
    (hf : BMeas f) (g : ι→ℝ) :
    (∫ x, (f x-meanBlock μ c f x)*g (c x) ∂μ)=0 := by
  classical
  have hm (i : ι) : MeasurableSet (cell c i) := hc (measurableSet_singleton i)
  have hd : Pairwise (Disjoint on cell c) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ : c x=i := hx
    have h₂ : c x=j := hy
    exact hij (h₁.symm.trans h₂)
  have hu : (⋃ i, cell c i)=univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨c x,show c x=c x from rfl⟩
  have hb : BMeas (fun x => (f x-meanBlock μ c f x)*g (c x)) :=
    (hf.sub (block_bmeas μ c hc f)).mul (bmeas_comp_finite c hc g)
  have hcell (i : ι) :
      (∫ x in cell c i,(f x-meanBlock μ c f x)*g (c x) ∂μ)=0 := by
    have he : EqOn (fun x => (f x-meanBlock μ c f x)*g (c x))
        (fun x => (f x-meanCell μ c f i)*g i) (cell c i) := by
      intro x hx
      have hi : c x=i := hx
      simp [meanBlock,hi]
    rw [setIntegral_congr_fun (hm i) he,integral_mul_const,
      mean_zero μ c hc f hf i,zero_mul]
  rw [← setIntegral_univ,← hu,integral_iUnion_fintype hm hd
    (fun _ => (bMeas_integrable μ hb).integrableOn)]
  simp only [hcell,Finset.sum_const_zero]

#print axioms mean_orthogonal
end SparseHalfGraphon
