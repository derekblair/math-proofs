import GeometricBandShellPair
import GeometricShellParameter
import GeometricCapGapEventual

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
local notation "S" => UnitSphere (SphereAmbient (Fin 1) W)

theorem shell_band_probability_bounds (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (t w : ℝ) (tp : 0<t) (ts : t≤1/8) (r3 : 3≤(m:ℝ)/2)
    (dense : 1≤4*((m:ℝ)/2)*t^2) (wide : 1/(4*((m:ℝ)/2)*t)≤w)
    (hi : t+w≤1) (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) :
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let A := shellBand t w
    0<σ.real A ∧ σ Aᶜ≠0 ∧ σ.real (capPoints t a)≤(2*Real.exp 3)*σ.real A := by
  intro σ A
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  have dec : sphereHeight ⁻¹' Ici t=capPoints t a := by
    ext x
    change t≤sphereHeight x ↔ t≤⟪a.val,x.val⟫_ℝ
    rw [ha]
  have h := spherical_band_positive_fraction m dim t w tp ts r3 dense wide hi
  rw [dec] at h
  change σ (capPoints t a)≤ENNReal.ofReal (2*Real.exp 3)*σ A at h
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top σ A)) h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hr
  have c := capPoints_both_positive t (by linarith only [tp]) (by linarith only [ts]) a
  have pq : 0<σ.real (capPoints t a) := ENNReal.toReal_pos c.1.ne'
    (measure_ne_top σ _)
  have p : 0<σ.real A := by
    have l := pq.trans_le hr
    exact pos_of_mul_pos_right l (by positivity)
  have sub : A⊆capPoints t a := by
    intro x hx
    change t≤sphereHeight x ∧ sphereHeight x≤t+w at hx
    change t≤⟪a.val,x.val⟫_ℝ
    rw [←ha]
    exact hx.1
  have apos : 0<σ Aᶜ := c.2.trans_le (measure_mono (compl_subset_compl.2 sub))
  exact ⟨p,apos.ne',hr⟩

theorem shell_loss_constant_small :
    2*Real.exp (36-(100:ℝ))≤(1:ℝ)/1000000000000 := by
  have low : (2:ℝ)≤Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
  have h : (2:ℝ)^64≤Real.exp 64 := by
    have e := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) low 64
    simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using e
  have b : Real.exp (36-(100:ℝ))≤((2:ℝ)^64)⁻¹ := by
    rw [show (36:ℝ)-100=-64 by norm_num,Real.exp_neg]
    exact inv_anti₀ (by positivity) h
  have z := mul_le_mul_of_nonneg_left b (by norm_num : (0:ℝ)≤2)
  exact z.trans (by norm_num)

theorem shell_width_valid (t r : ℝ) (tp : 0<t) (ts : t≤1/40000)
    (rp : 0<r) (large : 100≤r*t^2) :
    let w := 100/(r*t)
    let c := t/(1+t)
    let s := 4*t*w
    0≤w ∧ w≤t ∧ 1/(4*r*t)≤w ∧ t+w≤1 ∧ 0<c ∧ c≤1/40000 ∧ 0≤s ∧ s≤c := by
  intro w c s
  have pw : 0≤w := by dsimp [w]; positivity
  have w1 : w≤t := (div_le_iff₀ (by positivity : 0<r*t)).2 (by nlinarith only [large])
  have cc : c≤t := (div_le_iff₀ (by positivity : 0<1+t)).2 (by nlinarith only [sq_nonneg t])
  refine ⟨pw,w1,?_,by linarith only [w1,ts],by dsimp [c]; positivity,cc.trans ts,
    by dsimp [s]; positivity,?_⟩
  · dsimp [w]
    rw [show 4*r*t=4*(r*t) by ring,←div_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · have z := mul_le_mul_of_nonneg_left w1 (show 0≤4*t by positivity)
    have a : 4*t*(1+t)≤1 := by
      have s2 := pow_le_pow_left₀ tp.le ts 2
      nlinarith only [s2,ts]
    have h := mul_le_mul_of_nonneg_left a tp.le
    have e : 4*t*t≤c := (le_div_iff₀ (by positivity : 0<1+t)).2 (by nlinarith only [h])
    exact z.trans e

#print axioms shell_band_probability_bounds
#print axioms shell_loss_constant_small
#print axioms shell_width_valid
end RobustFolkman.GeometricGap
