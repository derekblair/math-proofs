import GeometricRectangleRates

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set RMT
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

theorem sample_rectangle_uniform {D n m L : ℕ} (μ : Measure (Fin D)) [IsProbabilityMeasure μ]
    (K : Fin D→Fin D→ℝ) (bin : ∀ x y, K x y=0 ∨ K x y=1) (q : ℝ) (qp : 0<q) (q1 : q≤1)
    (hn : 0<n) (hD : 0<D) (nL : n≤L) (mL : m≤L) (Lq : 1≤(L:ℝ)*q)
    (row : ∀ y, μ.real {x | K x y=1}≤2*q)
    (features : ∀ x, ∑ j,(kernelFeature (fun x y => K x y-q) (fun z => (μ {z}).toReal) x j)^2≤3*q)
    (pop : ‖weightedKernel (fun x y => K x y-q) (fun z => (μ {z}).toReal)‖≤q/100) :
    let ν := Measure.pi (fun _ : Fin n => μ)
    let τ := Measure.pi (fun _ : Fin m => μ)
    (ν.prod τ).real {z : (Fin n→Fin D)×(Fin m→Fin D) |
      (L:ℝ)*q/50 < ‖crossBlock (fun x y => K x y-q) z.1 z.2‖}
      ≤ (2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000) := by
  intro ν τ
  let s := (L:ℝ)*q^2/10000
  let u := (L:ℝ)^2*q^2/10000
  let ρ := q/100
  let k := ⌈8*(L:ℝ)*q⌉₊
  let B := (n:ℝ)*q^2+(k:ℝ)
  let T := (n:ℝ)*ρ^2+s
  have Lp := hn.trans_le nL
  have LP : 0<(L:ℝ) := by exact_mod_cast Lp
  have nL' : (n:ℝ)≤L := by exact_mod_cast nL
  have mL' : (m:ℝ)≤L := by exact_mod_cast mL
  have TB : T≤(L:ℝ)*q^2/5000 := by
    have a := mul_le_mul_of_nonneg_right nL' (sq_nonneg ρ)
    dsimp [T,ρ,s] at *
    nlinarith only [a]
  have kb : 8*(L:ℝ)*q≤(k:ℝ) := Nat.le_ceil _
  have ku : (k:ℝ)<8*(L:ℝ)*q+1 := Nat.ceil_lt_add_one (by positivity)
  have Bp : 0<B := by dsimp [B]; positivity
  have BB : B≤10*(L:ℝ)*q := by
    have qq : q^2≤q := by nlinarith only [mul_nonneg qp.le (sub_nonneg.mpr q1)]
    have a := mul_le_mul nL' qq (sq_nonneg q) LP.le
    dsimp [B]
    linarith only [a,ku,Lq]
  have rt := sample_rectangle_tail (m:=m) (k:=k) μ K bin q (2*q) (3*q) ρ s u qp.le
    (by positivity) (by dsimp [ρ]; positivity) (by dsimp [s]; positivity) (by dsimp [u]; positivity)
    hD hn Bp row features pop
  have cmp : Real.sqrt ((m:ℝ)*T+u)≤(L:ℝ)*q/50 := by
    apply (Real.sqrt_le_iff).2 ⟨by positivity,?_⟩
    have h := mul_le_mul mL' TB (by dsimp [T,s,ρ]; positivity) LP.le
    dsimp [u]
    nlinarith only [h,mul_nonneg (sq_nonneg (L:ℝ)) (sq_nonneg q)]
  have h := ENNReal.toReal_mono (by
    apply ENNReal.add_ne_top.2
    constructor
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,ENNReal.ofReal_ne_top⟩
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) rt
  have a := rectangle_first_stage_rate D n L nL q qp q1 Lp
  have b := rectangle_second_stage_rate n m L nL mL q T B qp q1 Lp
    (by dsimp [T,s,ρ]; positivity) Bp TB BB
  have c := rectangle_truncation_rate n L k nL q (2*q) qp.le (by positivity) le_rfl kb
  have r0 : 0≤matrixBernsteinTailBound D ((n:ℝ)*(3*q)*ρ^2) (3*q+ρ^2) s := by unfold matrixBernsteinTailBound; positivity
  have r1 : 0≤matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) u := by unfold matrixBernsteinTailBound; positivity
  have r2 : 0≤Real.exp (2*(n:ℝ)*(2*q))/(2:ℝ)^k := by positivity
  have firstFin := ENNReal.ofReal_ne_top (r:=matrixBernsteinTailBound D ((n:ℝ)*(3*q)*ρ^2) (3*q+ρ^2) s)
  have secondFin := ENNReal.ofReal_ne_top (r:=matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) u)
  change (ν.prod τ).real {z | Real.sqrt ((m:ℝ)*T+u)<‖crossBlock (fun x y => K x y-q) z.1 z.2‖} ≤ _ at h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨firstFin,secondFin⟩)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top),
    ENNReal.toReal_add firstFin secondFin,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal r0,ENNReal.toReal_ofReal r1,ENNReal.toReal_ofReal r2] at h
  calc
    _ ≤ (ν.prod τ).real {z | Real.sqrt ((m:ℝ)*T+u)<‖crossBlock (fun x y => K x y-q) z.1 z.2‖} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun z hz => lt_of_le_of_lt cmp hz)
    _ ≤ _ := h
    _ ≤ _ := by
      have t : (m:ℝ)*(Real.exp (2*(n:ℝ)*(2*q))/(2:ℝ)^k)≤(L:ℝ)*Real.exp (-(L:ℝ)*q/1000000) := by
        refine (mul_le_mul mL' c r2 LP.le).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) LP.le)
        linarith only [mul_pos LP qp]
      dsimp [ρ,s] at *
      have w := add_le_add (add_le_add a b) t
      exact w.trans_eq (by ring)

#print axioms sample_rectangle_uniform
end RobustFolkman.GeometricGap
