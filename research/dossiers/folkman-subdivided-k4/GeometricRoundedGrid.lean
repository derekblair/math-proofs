import GeometricRoundedFinite
import GeometricQuantizedLaw

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

theorem spherical_grid_rounded_tail (n L : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (a : GridSphere (n+3))
    (large : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*t^2)
    (gap : Real.sqrt (squaredCapContraction n t)≤1/200) :
    let d := n+3
    let m := gridResolution n 20
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let q := σ.real (capPoints t a)
    let D := Fintype.card (GridCode d m)
    1≤(L:ℝ)*q →
    (Measure.pi (fun _ : Fin L => σ)).real {x |
      3*(L:ℝ)*q/50 < ‖centeredSample (quantizedCapKernel t a)
        q (fun i => gridCode d m (x i))‖}
      ≤ ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) := by
  classical
  intro d m σ q D Lq
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := gridLaw (m:=m) σ
  let K := quantizedCapKernel (m:=m) t a
  let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
  let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
  have dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=n+3 := by simp [d]
  have mp : 0<m := gridResolution_pos n 20
  have q1 : q≤1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=σ) (s:=capPoints t a))
    exact h.trans_eq ENNReal.toReal_one
  have lower := cap_simple_grid_lower n dim t ts a
  have convertL (c : ℝ) : c⁻¹*(1/2:ℝ)^n = 1/(c*(2:ℝ)^n) := by
    rw [div_pow,one_pow,one_div,one_div,mul_inv]
  have zlo : 1/(4*(2:ℝ)^n)≤Z := by
    rw [←convertL]
    norm_num
    exact lower.1
  have qlo : 1/(8*(2:ℝ)^n)≤q := by
    rw [←convertL]
    norm_num
    exact lower.2
  have qp : 0<q := (by positivity : 0<1/(8*(2:ℝ)^n)).trans_le qlo
  have rr := grid_resolution_strip n 20 q Z qlo zlo
  change 2*δ/Z≤(1/2:ℝ)^20*q^2 ∧ δ≤1/4 at rr
  have lo : -1≤t-δ := by linarith only [tp,rr.2]
  have hi : t+δ≤1 := by linarith only [ts,rr.2]
  have small : 2*δ/Z≤q^2 := (rr.1).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1/2:ℝ)^20≤1) (sq_nonneg q))
  have qs : q^2≤q := by nlinarith only [mul_nonneg qp.le (sub_nonneg.mpr q1)]
  have sym (i j : GridCode d m) : K i j=K j i :=
    capKernel_symm t (cellRepresentative a i) (cellRepresentative a j)
  have bin (i j : GridCode d m) : K i j=0 ∨ K i j=1 := by
    change capKernel t (cellRepresentative a i) (cellRepresentative a j)=0 ∨
      capKernel t (cellRepresentative a i) (cellRepresentative a j)=1
    rw [capKernel_eq_ite]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have row (y : GridCode d m) : ν.real {x | K x y=1}≤2*q := by
    let S := {x : GridCode d m | K x y=1}
    have eq : S=(↑(Finset.univ.filter (fun x => K x y=1)) : Set (GridCode d m)) := by
      ext x
      simp [S]
    have mg : ν S=∑ x ∈ Finset.univ.filter (fun x => K x y=1), ν {x} := by
      rw [eq,sum_measure_singleton]
    have rr' : ν.real S = ∑ x, (ν {x}).toReal*K y x := by
      unfold Measure.real
      rw [mg,ENNReal.toReal_sum (fun x _ => measure_ne_top ν _)]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      rcases bin x y with e|e
      · simp [←sym x y,e]
      · simp [←sym x y,e]
    rw [rr']
    simp_rw [show ∀ j : GridCode d m, (ν {j}).toReal=σ.real (gridCode d m ⁻¹' {j}) from gridLaw_atom σ]
    have r := quantized_row_upper n m mp t a y lo hi
    change (∑ j, σ.real (gridCode d m ⁻¹' {j})*K y j)≤q+2*δ/Z at r
    exact r.trans (by linarith only [small,qs])
  have feat (x : GridCode d m) : ∑ j,(kernelFeature (fun x y => K x y-q)
      (fun z => (ν {z}).toReal) x j)^2≤3*q := by
    have z := quantized_grid_feature_bound n m mp t a lo hi x
    exact z.trans (by linarith only [small,qs])
  have pop : ‖weightedKernel (fun x y => K x y-q) (fun z => (ν {z}).toReal)‖≤q/100 := by
    have z := quantized_centered_cap_operator n m mp t tp ts large dense a lo hi
    have eq : weightedKernel (fun x y => K x y-q) (fun z => (ν {z}).toReal)
      = Matrix.of (fun (i j : GridCode d m) => Real.sqrt (σ.real (gridCode d m ⁻¹' {i}))*
        Real.sqrt (σ.real (gridCode d m ⁻¹' {j}))*(K i j-q)) := by
      ext i j
      simp only [weightedKernel,kernelFeature,Matrix.of_apply]
      have e (j : GridCode d m) : (ν {j}).toReal=σ.real (gridCode d m ⁻¹' {j}) := gridLaw_atom σ j
      rw [e,e]
      ring
    rw [eq]
    have s : Real.sqrt (2*δ/Z)≤q/200 := by
      apply (Real.sqrt_le_iff).2 ⟨by positivity,?_⟩
      refine rr.1.trans ?_
      norm_num
      nlinarith only [sq_nonneg q]
    have l := mul_le_mul_of_nonneg_left gap qp.le
    exact z.trans (by linarith only [l,s])
  let B := {z : Fin L→GridCode d m | 3*(L:ℝ)*q/50<‖centeredSample K q z‖}
  have Bm : MeasurableSet B := (Set.to_countable B).measurableSet
  change (Measure.pi (fun _ : Fin L => σ)).real ((fun x : Fin L→GridSphere d => fun i => gridCode d m (x i)) ⁻¹' B)≤_
  unfold Measure.real
  rw [(gridSample_preserving (J:=Fin L) (m:=m) σ).measure_preimage Bm.nullMeasurableSet]
  exact rounded_finite_tail ν K sym bin q qp q1 Lq row feat pop

#print axioms spherical_grid_rounded_tail
end RobustFolkman.GeometricGap
