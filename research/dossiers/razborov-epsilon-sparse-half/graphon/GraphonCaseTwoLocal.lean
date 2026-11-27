import EnergyAlgebra

open MeasureTheory Set

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def weightedDegree (K : Kernel X) (a : X→ℝ) (y : X) :=
  ∫ x, a x*K.W (x,y) ∂μ

theorem energy_row (K : Kernel X) (a f : X→ℝ) (ha : BMeas a) (hf : BMeas f) :
    energyPair μ K a f=∫ y, f y*weightedDegree μ K a y ∂μ := by
  unfold energyPair
  rw [integral_prod_symm _ (energy_integrable μ K ha hf)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  unfold weightedDegree
  change (∫ x, a x*f y*K.W (x,y) ∂μ) = f y*(∫ x, a x*K.W (x,y) ∂μ)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

theorem energy_three (K : Kernel X) (a e f : X→ℝ) (t : ℝ)
    (ha : BMeas a) (he : BMeas e) (hf : BMeas f) :
    energyPair μ K (a+e+(fun x => t*f x)) (a+e+(fun x => t*f x)) =
      energyPair μ K a a + energyPair μ K e e + t^2*energyPair μ K f f +
        2*energyPair μ K a e + 2*t*energyPair μ K a f + 2*t*energyPair μ K e f := by
  let l : X→ℝ := fun x => t*f x
  have hl : BMeas l := hf.scale t
  have hae := ha.add he
  have hall := hae.add hl
  change energyPair μ K (a+e+l) (a+e+l)=_
  rw [energy_add_left μ K (a+e) l (a+e+l) hae hl hall,
    energy_add_left μ K a e (a+e+l) ha he hall]
  rw [energy_add_right μ K a (a+e) l ha hae hl,
    energy_add_right μ K e (a+e) l he hae hl,
    energy_add_right μ K l (a+e) l hl hae hl]
  rw [energy_add_right μ K a a e ha ha he,
    energy_add_right μ K e a e he ha he,
    energy_add_right μ K l a e hl ha he]
  simp only [l,energy_scale_left,energy_scale_right]
  rw [energy_symm μ K e a,energy_symm μ K f a,energy_symm μ K f e]
  ring

/-- The actual Case 2 fractional half, with all geometry represented by
its explicit allocations, not an assumed scalar cost bound. -/
theorem local_fractional_half (K : Kernel X) (a e f : X→ℝ)
    (ha : BMeas a) (he : BMeas e) (hf : BMeas f)
    (ha0 : ∀ x, 0≤a x) (he0 : ∀ x, 0≤e x) (hf0 : ∀ x, 0≤f x)
    (hcap : ∀ x, a x+e x+f x≤1)
    (hA : (∫ x, a x ∂μ)=2/5)
    (hEF : (∫ x, e x ∂μ)+(∫ x, f x ∂μ)=1/5)
    (he1 : (∫ x, e x ∂μ)≤1/10)
    (haa : energyPair μ K a a=0) (hee : energyPair μ K e e=0)
    (haf : energyPair μ K a f≤(1/5)*(∫ x, f x ∂μ))
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle K z=0) :
    let h := 1/10-(∫ x, e x ∂μ)
    let R := (1/5)*(∫ x, e x ∂μ)-energyPair μ K a e
    beta μ K-1/50≤h/10-(3/4)*h^2-R := by
  dsimp
  let E := ∫ x, e x ∂μ
  let F := ∫ x, f x ∂μ
  let h := 1/10-E
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
        change 2/5+E+t*F=1/2
        rw [hl]
        dsimp [h]
        ring }
  have hβ : beta μ K≤halfEnergy μ K H := csInf_le (range_bdd μ K) ⟨H,rfl⟩
  rw [halfEnergy_as_pair] at hβ
  change beta μ K≤energyPair μ K (a+e+_) (a+e+_)/2 at hβ
  rw [energy_three μ K a e f t ha he hf,haa,hee] at hβ
  have hm : energyPair μ K f f/2≤F^2/4 := mantel_allocation μ K f hf.1 hf0 hF₁ htri
  have hmulM := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
  have hcross := energy_cross_bound μ K e f he hf he0 hf0
  have hmulC := mul_le_mul_of_nonneg_left hcross hlower
  have hmulAF := mul_le_mul_of_nonneg_left haf hlower
  change t*(energyPair μ K a f)≤t*((1/5)*F) at hmulAF
  change t*(energyPair μ K e f)≤t*(E*F) at hmulC
  have hEF₂ : t^2*F^2=h^2 := by rw [← mul_pow,hl]
  change beta μ K-1/50≤h/10-(3/4)*h^2-((1/5)*E-energyPair μ K a e)
  have heR : t*E*F=E*h := by rw [mul_comm t E,mul_assoc,hl]
  have haR : t*(1/5)*F=(1/5)*h := by rw [mul_comm t (1/5),mul_assoc,hl]
  dsimp [h] at heR haR hEF₂ ⊢
  nlinarith only [hβ,hmulM,hmulC,hmulAF,hEF₂,heR,haR]

#print axioms energy_three
#print axioms local_fractional_half
end SparseHalfGraphon
