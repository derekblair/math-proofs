import GraphonCaseTwoLocal

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The actual Case 2 fractional half, with all geometry represented by
its explicit allocations, not an assumed scalar cost bound. -/
theorem greedy_local_half (K : Kernel X) (a e f : X→ℝ)
    (ha : BMeas a) (he : BMeas e) (hf : BMeas f)
    (ha0 : ∀ x, 0≤a x) (he0 : ∀ x, 0≤e x) (hf0 : ∀ x, 0≤f x)
    (hcap : ∀ x, a x+e x+f x≤1)
    (b A : ℝ) (hα : A<1/2)
    (hA : (∫ x, a x ∂μ)=b)
    (hEF : (∫ x, e x ∂μ)+(∫ x, f x ∂μ)=1-A-b)
    (he1 : (∫ x, e x ∂μ)≤1/2-b)
    (hee : energyPair μ K e e=0)
    (haf : energyPair μ K a f≤(b/2)*(∫ x, f x ∂μ))
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    let E := ∫ x, e x ∂μ
    let h := 1/2-b-E
    beta μ K ≤ energyPair μ K a a/2 + energyPair μ K a e + (b/2)*h + E*h + h^2/4 := by
  dsimp
  let E := ∫ x, e x ∂μ
  let F := ∫ x, f x ∂μ
  let h := 1/2-b-E
  let t := h/F
  have h₀ : 0≤h := sub_nonneg.mpr he1
  have hF : 0<F := by dsimp [E,F] at *; linarith
  have hlower : 0≤t := div_nonneg h₀ hF.le
  have hupper : t≤1 := by
    apply (div_le_iff₀ hF).mpr
    dsimp [h,E,F] at *
    linarith
  have hl : t*F=h := by dsimp [t]; field_simp
  have hF₁ (x : X) : f x≤1 := by linarith [hcap x,ha0 x,he0 x]
  let H : Half μ :=
    { f := a+e+(fun x => t*f x)
      measurable_f := (ha.add he).1.add (hf.scale t).1
      nn := fun x => add_nonneg (add_nonneg (ha0 x) (he0 x)) (mul_nonneg hlower (hf0 x))
      le_one := fun x => by
        change a x+e x+t*f x≤1
        have hp := mul_le_mul_of_nonneg_right hupper (hf0 x)
        linarith [hcap x]
      mass_half := by
        change (∫ x, a x+e x+t*f x ∂μ)=1/2
        have hiAE : Integrable (fun x => a x+e x) μ :=
          (bMeas_integrable μ ha).add (bMeas_integrable μ he)
        rw [integral_add hiAE ((bMeas_integrable μ hf).const_mul t),
          integral_add (bMeas_integrable μ ha) (bMeas_integrable μ he),integral_const_mul,hA]
        change b+E+t*F=1/2
        rw [hl]
        dsimp [h]
        ring }
  have hβ : beta μ K≤halfEnergy μ K H := csInf_le (range_bdd μ K) ⟨H,rfl⟩
  rw [halfEnergy_as_pair] at hβ
  change beta μ K≤energyPair μ K (a+e+_) (a+e+_)/2 at hβ
  rw [energy_three μ K a e f t ha he hf,hee] at hβ
  have hm : energyPair μ K f f/2≤F^2/4 := mantel_allocation μ K f hf.1 hf0 hF₁ htri
  have hmulM := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
  have hcross := energy_cross_bound μ K e f he hf he0 hf0
  have hmulC := mul_le_mul_of_nonneg_left hcross hlower
  have hmulAF := mul_le_mul_of_nonneg_left haf hlower
  change t*(energyPair μ K a f)≤t*((b/2)*F) at hmulAF
  change t*(energyPair μ K e f)≤t*(E*F) at hmulC
  have hEF₂ : t^2*F^2=h^2 := by rw [← mul_pow,hl]
  change beta μ K ≤ energyPair μ K a a/2 + energyPair μ K a e + (b/2)*h + E*h + h^2/4
  have heR : t*E*F=E*h := by rw [mul_comm t E,mul_assoc,hl]
  have haR : t*(b/2)*F=(b/2)*h := by rw [mul_comm t (b/2),mul_assoc,hl]
  dsimp [h] at heR haR hEF₂ ⊢
  nlinarith only [hβ,hmulM,hmulC,hmulAF,hEF₂,heR,haR]

#print axioms greedy_local_half
end SparseHalfGraphon
