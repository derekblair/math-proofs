import GeometricCapLipEnergy
import GeometricCapSmoothing

namespace RobustFolkman.GeometricGap
open MeasureTheory
open scoped InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Exact population L² contraction for the bounded measurable tests
needed by finite quantization. Apply the Lipschitz estimate to Pf,
then use symmetry and Cauchy–Schwarz to bound Pf itself. -/
theorem cap_l2_contraction_bounded (n : ℕ) (dim : Module.finrank ℝ E=n+3)
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (large : 3≤(n:ℝ)/2)
    (dense : 1≤4*((n:ℝ)/2)*t^2) (a : UnitSphere E)
    (f : UnitSphere E→ℝ) (fm : Measurable f) (B : ℝ) (B0 : 0≤B) (bd : ∀ x, ‖f x‖≤B)
    (center : ∫ x,f x ∂uniformSphere (volume : Measure E)=0) :
    let σ := uniformSphere (volume : Measure E)
    energyNorm σ (capAverage t f)≤Real.sqrt (squaredCapContraction n t)*energyNorm σ f := by
  intro σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have t0 : -1<t := by linarith only [tp]
  have t1 : t<1 := by linarith only [ts]
  let g := capAverage t f
  let h := capAverage t g
  let ρ := Real.sqrt (squaredCapContraction n t)
  have ρ0 : 0≤ρ := Real.sqrt_nonneg _
  have gm := capAverage_measurable t a f fm
  have gb := capAverage_bound t t0 t1 f B bd
  have hm := capAverage_measurable t a g gm
  have hb := capAverage_bound t t0 t1 g B gb
  have z : ∫ x,g x ∂σ=0 := (capAverage_stationary_bounded t t0 t1 a f fm B B0 bd).trans center
  obtain ⟨L,lip⟩ := capAverage_smoothing n dim t tp ts a f fm B B0 bd
  have gc : energyNorm σ h≤ρ*energyNorm σ g :=
    cap_l2_contraction_lipschitz n dim t tp ts large dense a g L lip z
  have e := capAverage_symmetry_bounded t a f g fm gm B B B0 B0 bd gb
  have b : (energyNorm σ g)^2≤energyNorm σ f*energyNorm σ h := by
    rw [energyNorm_sq]
    simp_rw [pow_two]
    change (∫ x,g x*g x ∂σ)≤_
    change (∫ x,f x*h x ∂σ)=∫ x,g x*g x ∂σ at e
    rw [←e]
    exact energy_cauchy σ f h
      (MemLp.of_bound fm.aestronglyMeasurable B (ae_of_all _ bd))
      (MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ hb))
  have gn : 0≤energyNorm σ g := Real.sqrt_nonneg _
  change energyNorm σ g≤ρ*energyNorm σ f
  by_cases g0 : energyNorm σ g=0
  · rw [g0]
    exact mul_nonneg ρ0 (Real.sqrt_nonneg _)
  · have gp := lt_of_le_of_ne gn (Ne.symm g0)
    apply (le_of_mul_le_mul_right ?_ gp)
    have p : energyNorm σ f*energyNorm σ h≤ energyNorm σ f*(ρ*energyNorm σ g) :=
      mul_le_mul_of_nonneg_left gc (Real.sqrt_nonneg _)
    nlinarith only [b,p]

#print axioms cap_l2_contraction_bounded
end RobustFolkman.GeometricGap
