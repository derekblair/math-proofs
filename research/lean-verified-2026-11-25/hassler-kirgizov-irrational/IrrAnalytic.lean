import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

open scoped goldenRatio BigOperators
open Filter Topology
namespace FibPopularity
open Real

noncomputable def r : ℝ := ψ / φ
noncomputable def t : ℝ := Real.sqrt 5

lemma t_pos : 0 < t := by unfold t; positivity
lemma r_abs : |r| < 1 := by
  rw [r,abs_div,abs_of_pos goldenRatio_pos,div_lt_one goldenRatio_pos]
  have h : |ψ| < 1 := abs_lt.mpr ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
  linarith [one_lt_goldenRatio]
lemma r_ne : r ≠ 1 := by
  have h := r_abs
  intro e
  rw [e,abs_one] at h
  linarith

lemma fib_scaled (j : Nat) :
    (Nat.fib j : ℝ) = (φ^j / t) * (1-r^j) := by
  have hr : r^j = ψ^j / φ^j := div_pow _ _ _
  rw [coe_fib_eq,hr]
  change (φ^j-ψ^j)/t = (φ^j/t)*(1-ψ^j/φ^j)
  field_simp [goldenRatio_ne_zero,ne_of_gt t_pos]

noncomputable def conv (z : Nat) : ℝ :=
  ∑ i ∈ Finset.range (z+1), (Nat.fib (i+1) : ℝ) * Nat.fib (z-i+1)

lemma sum_reverse_pow (z : Nat) :
    (∑ i ∈ Finset.range (z+1), r^(z-i+1)) = ∑ i ∈ Finset.range (z+1), r^(i+1) := by
  apply Finset.sum_bij (fun i hi => z-i)
  · intro i hi
    simp only [Finset.mem_range] at *
    omega
  · intro a ha b hb h
    simp only [Finset.mem_range] at *
    omega
  · intro b hb
    simp only [Finset.mem_range] at *
    exact ⟨z-b,by omega,by omega⟩
  · intro a ha
    rfl

lemma conv_formula (z : Nat) :
    conv z = (φ^(z+2)/t^2) *
      ((z+1:ℝ)*(1+r^(z+2)) - 2*(∑ i ∈ Finset.range (z+1), r^(i+1))) := by
  unfold conv
  calc
    _ = ∑ i ∈ Finset.range (z+1), (φ^(z+2)/t^2) * ((1-r^(i+1))*(1-r^(z-i+1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [fib_scaled,fib_scaled]
      have he : φ^(z+2)=φ^(i+1)*φ^(z-i+1) := by rw [←pow_add]; congr 1; omega
      rw [he]
      ring
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      have hinner :
          (∑ i ∈ Finset.range (z+1), (1-r^(i+1))*(1-r^(z-i+1))) =
          (∑ i ∈ Finset.range (z+1), ((1+r^(z+2))-r^(i+1)-r^(z-i+1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have he : r^(z+2)=r^(i+1)*r^(z-i+1) := by rw [←pow_add]; congr 1; omega
        rw [he]
        ring
      rw [hinner,Finset.sum_sub_distrib,Finset.sum_sub_distrib, sum_reverse_pow]
      simp
      ring

lemma coeff_mul (z : Nat) : φ^(z+5) = φ^(z+2)*φ^3 := by rw [←pow_add]

lemma conv_norm (z : Nat) :
    conv z / (((z:ℝ)+4)*Nat.fib (z+5)) =
    (1/(φ^3*t)) *
      ((((z+1:ℝ)/((z:ℝ)+4)) * (1 + r^(z+2)) -
         (2 / ((z:ℝ)+4)) * (∑ i ∈ Finset.range (z+1), r^(i+1))) /
      (1 - r^(z+5))) := by
  rw [conv_formula,fib_scaled,coeff_mul]
  have h4 : (z:ℝ)+4 ≠ 0 := by positivity
  have hφ : φ^(z+2) ≠ 0 := pow_ne_zero _ goldenRatio_ne_zero
  have ht := ne_of_gt t_pos
  by_cases hz : 1 - r^(z+5) = 0
  · simp [hz]
  · field_simp [h4,hφ,ht,goldenRatio_ne_zero,hz] <;> ring

lemma finite_geom (z : Nat) :
    (∑ i ∈ Finset.range (z+1), r^(i+1)) = r*((r^(z+1)-1)/(r-1)) := by
  simp_rw [pow_succ]
  rw [←Finset.sum_mul,geom_sum_eq r_ne]
  ring

lemma shifted_pow (k : Nat) : Tendsto (fun z : Nat => r^(z+k)) atTop (𝓝 0) := by
  simp_rw [pow_add]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one r_abs).mul tendsto_const_nhds

lemma cast_plus_four : Tendsto (fun n : Nat => (n:ℝ)+4) atTop atTop :=
  Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds

theorem conv_limit :
    Tendsto (fun z : Nat => conv z / (((z:ℝ)+4)*Nat.fib (z+5))) atTop (𝓝 (1/(φ^3*t))) := by
  have inv : Tendsto (fun z : Nat => (1:ℝ)/((z:ℝ)+4)) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp cast_plus_four |>.congr (by intro a; simp [one_div])
  have A : Tendsto (fun z : Nat => (z+1:ℝ)/((z:ℝ)+4)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun z : Nat => (1:ℝ)-3*(1/((z:ℝ)+4))) atTop (𝓝 1) := by
      simpa only [mul_zero,sub_zero] using
        (tendsto_const_nhds (x := (1:ℝ))).sub ((tendsto_const_nhds (x := (3:ℝ))).mul inv)
    apply h0.congr
    intro z
    have hh : (z:ℝ)+4 ≠ 0 := by positivity
    change 1-3*(1/((z:ℝ)+4))=(z+1:ℝ)/((z:ℝ)+4)
    field_simp
    ring
  have B : Tendsto (fun z : Nat => (1:ℝ)+r^(z+2)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (shifted_pow 2)
  have C : Tendsto (fun z : Nat => (2:ℝ)/((z:ℝ)+4)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (2:ℝ))).mul inv
  have D : Tendsto (fun z : Nat => ∑ i ∈ Finset.range (z+1), r^(i+1)) atTop (𝓝 (r*((0-1)/(r-1)))) := by
    simp_rw [finite_geom]
    exact tendsto_const_nhds.mul (((shifted_pow 1).sub tendsto_const_nhds).div_const (r-1))
  have E : Tendsto (fun z : Nat => (1:ℝ)-r^(z+5)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (shifted_pow 5)
  simp_rw [conv_norm]
  simpa only [Pi.div_apply,mul_one,zero_mul,sub_zero,div_one] using
    (tendsto_const_nhds (x := (1/(φ^3*t):ℝ))).mul (((A.mul B).sub (C.mul D)).div E (by norm_num))

theorem constant_irrational : Irrational (1/(φ^3*t)) := by
  have ht : t^2=5 := by unfold t; exact sq_sqrt (by norm_num)
  have he : 1/(φ^3*t) = 1-(2/5:ℝ)*t := by
    have hφ : φ = (1+t)/2 := rfl
    have hne : φ^3*t ≠ 0 := ne_of_gt (mul_pos (pow_pos goldenRatio_pos _) t_pos)
    apply (div_eq_iff hne).mpr
    rw [hφ]
    nlinarith [congrArg (fun x : ℝ => x*t) ht, congrArg (fun x : ℝ => x*t^2) ht,
        congrArg (fun x : ℝ => x*t^3) ht]
  rw [he]
  have h : Irrational t := (show Nat.Prime 5 by norm_num).irrational_sqrt
  simpa using ((h.ratCast_mul (show (2/5:ℚ) ≠ 0 by norm_num)).ratCast_sub 1)

end FibPopularity
