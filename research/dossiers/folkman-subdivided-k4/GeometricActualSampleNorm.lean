import GeometricRoundedGrid
import GeometricSampleQuantization

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

/-- Actual spherical-cap adjacency, not its grid approximation. This is
the only spectral input needed for the tight residual graph cut. -/
theorem spherical_actual_sample_tail (n N : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (a : GridSphere (n+3))
    (large : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*t^2)
    (gap : Real.sqrt (squaredCapContraction n t)≤1/200) :
    let d := n+3
    let m := gridResolution n 20
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let q := σ.real (capPoints t a)
    let D := Fintype.card (GridCode d m)
    let L := N+1
    100≤(L:ℝ)*q →
    (Measure.pi (fun _ : Fin L => σ)).real {x |
      4*(L:ℝ)*q/50 < ‖centeredSample (capKernel t) q x‖}
      ≤ ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) +
        (L:ℝ)*Real.exp (-(L:ℝ)*q/1000) := by
  classical
  intro d m σ q D L Lq
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := Measure.pi (fun _ : Fin L => σ)
  let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
  let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=n+3 := by simp [d]
  have base := cap_simple_grid_lower n dim t ts a
  have conv (c : ℝ) : c⁻¹*(1/2:ℝ)^n = 1/(c*(2:ℝ)^n) := by
    rw [div_pow,one_pow,one_div,one_div,mul_inv]
  have zl : 1/(4*(2:ℝ)^n)≤Z := by rw [←conv]; norm_num; exact base.1
  have ql : 1/(8*(2:ℝ)^n)≤q := by rw [←conv]; norm_num; exact base.2
  have qp : 0<q := (by positivity : 0<1/(8*(2:ℝ)^n)).trans_le ql
  have q1 : q≤1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=σ) (s:=capPoints t a))
    exact h.trans_eq ENNReal.toReal_one
  have grid := grid_resolution_strip n 20 q Z ql zl
  change 2*δ/Z≤(1/2:ℝ)^20*q^2 ∧ δ≤1/4 at grid
  have lo : -1≤t-δ := by linarith only [tp,grid.2]
  have hi : t+δ≤1 := by linarith only [ts,grid.2]
  have p0 : 0≤2*δ/Z := by dsimp [δ,Z]; positivity
  have pb : 2*δ/Z≤2*(q/1000) := by
    have qsq : q^2≤q := by nlinarith only [mul_nonneg qp.le (sub_nonneg.mpr q1)]
    have h := mul_le_mul_of_nonneg_left qsq (by norm_num : (0:ℝ)≤(1/2)^20)
    norm_num at h
    linarith only [grid.1,h,qp]
  let k := ⌊(L:ℝ)*q/50⌋₊
  have ku : (k:ℝ)≤(L:ℝ)*q/50 := Nat.floor_le (by positivity)
  have kd : (L:ℝ)*q/50 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have kl : 8*(L:ℝ)*(q/1000)≤(k:ℝ) := by nlinarith only [kd,Lq]
  have rt := rectangle_truncation_rate N L k (by dsimp [L]; omega)
    (q/1000) (2*δ/Z) (by positivity) p0 pb kl
  let A := {x : Fin L→GridSphere d | (L:ℝ)*q/50<‖sampleCapError (m:=m) t a x‖}
  have er : ν.real A≤(L:ℝ)*Real.exp (-(L:ℝ)*q/1000) := by
    have h := sample_cap_quantization_tail n m N k (gridResolution_pos n 20) t a lo hi
    have incl : A ⊆ {x | (k:ℝ)<‖sampleCapError (m:=m) t a x‖} := fun _ hx => ku.trans_lt hx
    have b := (measure_mono (μ:=ν) incl).trans h
    have z := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.natCast_ne_top N,ENNReal.one_ne_top⟩) ENNReal.ofReal_ne_top) b
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at z
    have ncast : (N+1:ℝ≥0∞).toReal=(L:ℝ)  := by
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top N) ENNReal.one_ne_top,
        ENNReal.toReal_natCast,ENNReal.toReal_one]
      push_cast [L]
      rfl
    rw [ncast] at z
    exact z.trans (mul_le_mul_of_nonneg_left (rt.trans_eq (by congr 1; ring)) (Nat.cast_nonneg L))
  let B := {x : Fin L→GridSphere d | 3*(L:ℝ)*q/50<‖centeredSample (quantizedCapKernel (m:=m) t a)
    q (fun i => gridCode d m (x i))‖}
  have br := spherical_grid_rounded_tail n L t tp ts a large dense gap (by linarith only [Lq])
  have incl : {x : Fin L→GridSphere d | 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖}⊆ A∪B := by
    intro x hx
    by_contra! hn
    have ar : ‖sampleCapError (m:=m) t a x‖≤(L:ℝ)*q/50 := le_of_not_gt (fun hh => hn (Or.inl hh))
    have rr : ‖centeredSample (quantizedCapKernel (m:=m) t a) q
      (fun i => gridCode d m (x i))‖≤3*(L:ℝ)*q/50 := le_of_not_gt (fun hh => hn (Or.inr hh))
    have eq : centeredSample (capKernel t) q x =
        centeredSample (quantizedCapKernel (m:=m) t a) q (fun i => gridCode d m (x i)) -
        sampleCapError (m:=m) t a x := by
      ext i j
      by_cases h : i=j
      · subst j; simp [centeredSample,sampleCapError]
      · simp only [centeredSample,sampleCapError,h,ite_false,Matrix.of_apply,Matrix.sub_apply,d]
        ring
    have nm := norm_sub_le (centeredSample (quantizedCapKernel (m:=m) t a) q
      (fun i => gridCode d m (x i))) (sampleCapError (m:=m) t a x)
    rw [←eq] at nm
    change 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖ at hx
    linarith only [ar,rr,nm,hx]
  have u := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top ν A,measure_ne_top ν B⟩)
    ((measure_mono (μ:=ν) incl).trans (measure_union_le A B))
  rw [ENNReal.toReal_add (measure_ne_top ν A) (measure_ne_top ν B)] at u
  exact u.trans ((add_le_add er br).trans_eq (add_comm _ _))

#print axioms spherical_actual_sample_tail
end RobustFolkman.GeometricGap
