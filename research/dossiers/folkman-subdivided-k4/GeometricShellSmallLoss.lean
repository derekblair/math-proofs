import GeometricShellRemoval
import GeometricShellScales

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
local notation "S" => UnitSphere (SphereAmbient (Fin 1) W)

noncomputable def shellTolerance : ℝ := 1/1000000000000

theorem shell_small_loss_bound (n : ℕ) (dim : Module.finrank ℝ W=n+3)
    (dS : Module.finrank ℝ (SphereAmbient (Fin 1) W)=n+4)
    (t : ℝ) (tp : 0<t) (ts : t≤1/40000)
    (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) (b : UnitSphere W)
    (large : 36≤(n:ℝ)/2) (width : 100≤(((n+1:ℕ):ℝ)/2)*t^2)
    (r3 : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*(t/(1+t))^2)
    (sm : ∀ r : ℝ, 0<r → let c := t/(1+t); let w := 100/(r*t); let s := 4*t*w;
      (4*r*c*s)*Real.exp (3+4*r*c*s)≤shellTolerance) :
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let τ := uniformSphere (volume : Measure W)
    let r := (((n+1:ℕ):ℝ)/2)
    let w := 100/(r*t)
    let c := t/(1+t)
    let P := σ.real (shellBand t w)
    let q := τ.real (capPoints c b)
    0<P ∧ σ (shellBand t w)ᶜ≠0 ∧ σ.real (capPoints t a)≤(2*Real.exp 3)*P ∧
      (σ.prod σ).real (triangleAt t a\shellPair t w c)≤(5*shellTolerance)*P^2*q := by
  intro σ τ r w c P q
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  have rp : 0<r := by dsimp [r]; positivity
  have ts' : t≤1/8 := ts.trans (by norm_num)
  obtain ⟨w0,wt,wide,wh,cp,cs,s0,st⟩ := shell_width_valid t r tp ts rp width
  have dim' : Module.finrank ℝ W=(n+1)+2 := by omega
  have dS' : Module.finrank ℝ (SphereAmbient (Fin 1) W)=3+n+1 := by rw [dS]; omega
  change 100≤r*t^2 at width
  have ds : 1≤4*r*t^2 := by linarith only [width]
  obtain ⟨pp,pa,h⟩ := shell_band_probability_bounds (n+1) dim' t w tp ts'
    (by push_cast; linarith only [large]) ds wide wh a ha
  refine ⟨pp,pa,h,?_⟩
  have pn : σ (shellBand t w)≠0 := (ENNReal.toReal_pos_iff.1 pp).1.ne'
  let R := (n:ℝ)/2
  let A := 100*R/r
  have rR : r = R+1/2 := by dsimp [r,R]; push_cast; ring
  have Rp : 0<R := by dsimp [R]; linarith only [large]
  have A90 : 90≤A := by
    apply (le_div_iff₀ rp).2
    rw [rR]
    dsimp [R]
    linarith only [large]
  have largeR : 1≤R*t^2 := by
    have le : r≤2*R := by rw [rR]; dsimp [R]; linarith only [large]
    have z := mul_le_mul_of_nonneg_right le (sq_nonneg t)
    nlinarith only [width,z]
  have ww : A/(R*t)=w := by
    dsimp [A,w]
    field_simp [Rp.ne',rp.ne',tp.ne']
  have lo := fixed_root_shell_loss n dS' t A tp ts' large largeR a
  change (σ.prod σ) (lostRootTriangle t (A/(R*t)) a)≤
    2*ENNReal.ofReal (Real.exp (36-A))*(σ.prod σ) (triangleAt t a) at lo
  rw [ww] at lo
  have lor := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num : (2:ℝ≥0∞)≠⊤) ENNReal.ofReal_ne_top)
    (measure_ne_top (σ.prod σ) _)) lo
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_nonneg _)] at lor
  have factor : 2*Real.exp (36-A)≤shellTolerance := by
    have h : Real.exp (36-A)≤Real.exp (-54) := Real.exp_le_exp.2 (by linarith only [A90])
    have before : (2:ℝ)≤Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    have high : (2:ℝ)^54≤Real.exp 54 := by
      have z := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) before 54
      simpa only [←Real.exp_nat_mul,Nat.cast_ofNat,mul_one] using z
    have inv : Real.exp (-54)≤((2:ℝ)^54)⁻¹ := by rw [Real.exp_neg]; exact inv_anti₀ (by positivity) high
    exact (mul_le_mul_of_nonneg_left (h.trans inv) (by norm_num)).trans (by norm_num [shellTolerance])
  have loss : (σ.prod σ).real (lostRootTriangle t w a)≤shellTolerance*(σ.prod σ).real (triangleAt t a) := by
    have h : (σ.prod σ).real (lostRootTriangle t w a)≤
        2*Real.exp (36-A)*(σ.prod σ).real (triangleAt t a) := by
      unfold Measure.real
      simpa only [ENNReal.toReal_ofNat] using lor
    exact h.trans (mul_le_mul_of_nonneg_right factor ENNReal.toReal_nonneg)
  let s := 4*t*w
  have nc : (n:ℝ)/2≤r := by dsimp [r]; push_cast; linarith
  have c0 : 0≤c := cp.le
  have sr : 4*((n:ℝ)/2)*c*s≤4*r*c*s := by
    have x : 0≤4*c*s := by positivity
    have h := mul_le_mul_of_nonneg_right nc x
    nlinarith only [h]
  have sr0 : 0≤4*((n:ℝ)/2)*c*s := by positivity
  have sm' : (4*((n:ℝ)/2)*c*s)*Real.exp (3+4*((n:ℝ)/2)*c*s)≤shellTolerance := by
    have e : Real.exp (3+4*((n:ℝ)/2)*c*s)≤Real.exp (3+4*r*c*s) := Real.exp_le_exp.2 (by linarith only [sr])
    have h := mul_le_mul sr e (Real.exp_nonneg _) (sr0.trans sr)
    exact h.trans (sm r rp)
  have gap := pairCap_gap_mass n dim c s shellTolerance cp (cs.trans (by norm_num)) r3 dense s0 st sm' b
  have result := shell_removed_pair_mass (n+1) dim' t w shellTolerance shellTolerance tp ts' w0 wt
    (by norm_num [shellTolerance]) (by norm_num [shellTolerance])
    (by norm_num [shellTolerance]) (by norm_num [shellTolerance]) a ha b pn loss gap
  convert result using 1 <;> ring

#print axioms shell_small_loss_bound
end RobustFolkman.GeometricGap
