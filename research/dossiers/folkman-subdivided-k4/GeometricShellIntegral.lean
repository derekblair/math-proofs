import GeometricShellWeight
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace RobustFolkman.GeometricGap
open MeasureTheory Set
open scoped ENNReal

theorem lintegral_exp_halfline (k s : ℝ) (hk : 0<k) :
    (∫⁻ x : ℝ in Ici s, ENNReal.ofReal (Real.exp (-k*x))) =
      ENNReal.ofReal (Real.exp (-k*s)/k) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.mpr (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) s))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  rw [integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hk)]
  simp

abbrev ThreeReals := ℝ × ℝ × ℝ

noncomputable def shiftedExponential (k : ℝ) (p : ThreeReals) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-k*(p.1+p.2.1+p.2.2)))

theorem orthant_exp_integral (k a b c : ℝ) (hk : 0<k) :
    (∫⁻ p in Ici a ×ˢ (Ici b ×ˢ Ici c), shiftedExponential k p) =
      ENNReal.ofReal (Real.exp (-k*(a+b+c))/k^3) := by
  let f := fun x : ℝ => ENNReal.ofReal (Real.exp (-k*x))
  have mf : Measurable f := by dsimp [f]; fun_prop
  have fact (p : ThreeReals) : shiftedExponential k p = f p.1 * (f p.2.1 * f p.2.2) := by
    unfold shiftedExponential
    rw [show -k*(p.1+p.2.1+p.2.2)=(-k*p.1)+((-k*p.2.1)+(-k*p.2.2)) by ring]
    dsimp [f]
    rw [Real.exp_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [fact]
  change (∫⁻ p, f p.1 * (f p.2.1 * f p.2.2)
      ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)).restrict
        (Ici a ×ˢ (Ici b ×ˢ Ici c))) = _
  rw [←Measure.prod_restrict,←Measure.prod_restrict]
  have mf2 : Measurable (fun p : ℝ×ℝ => f p.1 * f p.2) :=
    (mf.comp measurable_fst).mul (mf.comp measurable_snd)
  rw [lintegral_prod_mul mf.aemeasurable mf2.aemeasurable,
    lintegral_prod_mul mf.aemeasurable mf.aemeasurable]
  dsimp [f]
  rw [lintegral_exp_halfline k a hk,lintegral_exp_halfline k b hk,lintegral_exp_halfline k c hk,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show -k*(a+b+c)=(-k*a)+((-k*b)+(-k*c)) by ring,Real.exp_add,Real.exp_add]
  ring

#print axioms orthant_exp_integral
end RobustFolkman.GeometricGap
