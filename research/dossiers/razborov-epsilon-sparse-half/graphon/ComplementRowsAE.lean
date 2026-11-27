import GraphonMantel

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

/-- Two edge-disjoint fractional rows with at least half the ambient mass
are the exact complementary indicator rows. -/
theorem complementary_rows (ν : Measure X) [IsFiniteMeasure ν]
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ x, 0≤f x) (hf₁ : ∀ x, f x≤1)
    (hg₀ : ∀ x, 0≤g x) (hg₁ : ∀ x, g x≤1)
    (hfg : ∀ᵐ x ∂ν, f x*g x=0)
    (ha : mass ν/2≤ ∫ x, f x ∂ν)
    (hb : mass ν/2≤ ∫ x, g x ∂ν) :
    ∀ᵐ x ∂ν, (f x=0 ∧ g x=1) ∨ (f x=1 ∧ g x=0) := by
  have hsum : ∀ᵐ x ∂ν, f x+g x≤1 := by
    filter_upwards [hfg] with x hx
    rcases mul_eq_zero.mp hx with hz | hz
    · simpa [hz] using hg₁ x
    · simpa [hz] using hf₁ x
  have iF := integrable_bounded ν hf hf₀ hf₁
  have iG := integrable_bounded ν hg hg₀ hg₁
  have i1 : Integrable (fun _ : X => (1:ℝ)) ν := integrable_const _
  have iH : Integrable (fun x => 1-f x-g x) ν := (i1.sub iF).sub iG
  have hp : 0 ≤ᵐ[ν] fun x => 1-f x-g x := by
    filter_upwards [hsum] with x hx
    dsimp
    linarith
  have hi : (∫ x, 1-f x-g x ∂ν)=0 := by
    have hnonneg := integral_nonneg_of_ae hp
    have he : (∫ x, 1-f x-g x ∂ν)=mass ν - (∫ x, f x ∂ν) - ∫ x, g x ∂ν := by
      have ii : Integrable (fun x => 1-f x) ν := i1.sub iF
      rw [integral_sub ii iG,integral_sub i1 iF,integral_const]
      simp [mass,smul_eq_mul]
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hp iH).mp hi
  filter_upwards [hz,hfg] with x h₁ h₂
  have h₁' : 1-f x-g x=0 := h₁
  rcases mul_eq_zero.mp h₂ with h₂ | h₂
  · exact Or.inl ⟨h₂, by linarith⟩
  · exact Or.inr ⟨by linarith, h₂⟩

/-- On almost every outside edge of a triangle-free kernel, saturated
anchor-degree rows are exact complementary indicator rows. -/
theorem edge_complement (μ ν ω : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ω] (hν : ν ≪ μ) (hω : ω ≪ μ) (K : Kernel X)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0)
    (hrows : ∀ᵐ x ∂ω, mass ν/2≤deg ν K x) :
    ∀ᵐ z ∂ω.prod ω, K.W z=0 ∨
      ∀ᵐ y ∂ν, (K.W (z.1,y)=0 ∧ K.W (z.2,y)=1) ∨
        (K.W (z.1,y)=1 ∧ K.W (z.2,y)=0) := by
  have hp : ∀ᵐ z ∂(ω.prod ω).prod ν, triangle K z=0 :=
    htri.filter_mono ((hω.prod hω).prod hν).ae_le
  have hpair : ∀ᵐ z ∂ω.prod ω,
      mass ν/2≤deg ν K z.1 ∧ mass ν/2≤deg ν K z.2 := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hrows] with x hx
      filter_upwards [hrows] with y hy
      exact ⟨hx,hy⟩
    · exact (measurableSet_le measurable_const ((deg_measurable ν K).comp measurable_fst)).inter
        (measurableSet_le measurable_const ((deg_measurable ν K).comp measurable_snd))
  filter_upwards [Measure.ae_ae_of_ae_prod hp,hpair] with z hz hzs
  by_cases h0 : K.W z=0
  · exact Or.inl h0
  · right
    apply complementary_rows ν (fun y => K.W (z.1,y)) (fun y => K.W (z.2,y))
      (rowMeasurable K z.1) (rowMeasurable K z.2) (fun y => K.nonneg _) (fun y => K.le_one _)
      (fun y => K.nonneg _) (fun y => K.le_one _) _ hzs.1 hzs.2
    filter_upwards [hz] with y hy
    have he : K.W z*(K.W (z.1,y)*K.W (z.2,y))=0 := by
      rw [← mul_assoc]
      exact hy
    exact (mul_eq_zero.mp he).resolve_left h0

#print axioms complementary_rows
#print axioms edge_complement
end SparseHalfGraphon
