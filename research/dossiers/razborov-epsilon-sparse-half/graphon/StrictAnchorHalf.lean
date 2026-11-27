import MarkedLimits

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Two independent allocations, with masses 2/5 and 1/10,
give a strict sparse half as soon as their cross energy is below 1/50. -/
theorem strict_two_independent_half (K : Kernel X) (a e : X → ℝ)
    (ha : BMeas a) (he : BMeas e) (h₀ : ∀ x, 0≤a x) (he₀ : ∀ x, 0≤e x)
    (h₁ : ∀ x, a x+e x≤1)
    (hA : (∫ x, a x ∂μ)=2/5) (hE : (∫ x, e x ∂μ)=1/10)
    (hAA : energyPair μ K a a=0) (hEE : energyPair μ K e e=0)
    (hAE : energyPair μ K a e<1/50) :
    beta μ K<1/50 := by
  let H : Half μ := ⟨a+e,(ha.add he).1,fun x => add_nonneg (h₀ x) (he₀ x),h₁,by
    rw [integral_add' (bMeas_integrable μ ha) (bMeas_integrable μ he),hA,hE]
    norm_num⟩
  have hh : halfEnergy μ K H = energyPair μ K a e := by
    rw [halfEnergy_as_pair]
    change energyPair μ K (a+e) (a+e)/2=_
    rw [energy_add_left μ K a e (a+e) ha he (ha.add he),
      energy_add_right μ K a a e ha ha he, energy_add_right μ K e a e he ha he,
      hAA,hEE,energy_symm μ K e a]
    ring
  exact (csInf_le (range_bdd μ K) ⟨H,rfl⟩).trans_lt (hh.symm ▸ hAE)

/-- If a neighbor allocation lies on the eligible degree interval,
positive weighted deficit gives strictly smaller cross energy. -/
theorem strict_anchor_deficit (K : Kernel X) (a e : X → ℝ)
    (ha : Measurable a) (he : BMeas e) (h₀ : ∀ x, 0≤a x) (he₀ : ∀ x, 0≤e x)
    (h₁ : ∀ x, a x+e x≤1)
    (hA : (∫ x, a x ∂μ)=2/5) (hE : (∫ x, e x ∂μ)=1/10)
    (hAA : energyPair μ K a a=0) (hEE : energyPair μ K e e=0)
    (hZ : 0<defMass μ (reweight μ a) K e) :
    beta μ K<1/50 := by
  have ba := BMeas.of_unit ha h₀ (fun x=>by linarith [h₁ x,he₀ x])
  have : IsFiniteMeasure (reweight μ a) :=
    isFiniteMeasure_of_le μ (reweight_le μ a (fun x=>by linarith [h₁ x,he₀ x]))
  apply strict_two_independent_half μ K a e ba he h₀ he₀ h₁ hA hE hAA hEE
  rw [energy_row μ K a e ba he]
  simp only [weightedDegree_eq_reweight μ K a ha h₀]
  unfold defMass deficit at hZ
  have hI : Integrable (fun x => e x*deg (reweight μ a) K x) μ := bMeas_integrable μ (he.mul (deg_bmeas (reweight μ a) K))
  have hT := (bMeas_integrable μ he).mul_const (1/5)
  have hf : (fun x => e x * (1/5-deg (reweight μ a) K x)) =
      fun x=> e x*(1/5) - e x*deg (reweight μ a) K x := by
    funext x
    ring
  rw [hf,integral_sub hT hI,integral_mul_const,hE] at hZ
  linarith

#print axioms strict_two_independent_half
#print axioms strict_anchor_deficit
end SparseHalfGraphon
