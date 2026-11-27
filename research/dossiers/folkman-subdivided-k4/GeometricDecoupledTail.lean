import GeometricDecoupledNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset
open scoped BigOperators ENNReal
variable {J Ω H : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace Ω]
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- Average over random splits instead of taking a union over all splits.
This loses a freely chosen bad-fraction factor, not an exponential factor. -/
theorem decoupled_norm_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Matrix J J ℝ →ₗ[ℝ] H) (A : Ω → Matrix J J ℝ)
    (diag : ∀ x i, A x i i=0) (g B η p : ℝ) (g0 : 0≤g) (B0 : 0≤B) (ηp : 0<η)
    (size : ∀ x b, ‖T (crossPart (A x) b)‖≤B)
    (badm : ∀ b, MeasurableSet {x | g<‖T (crossPart (A x) b)‖})
    (badt : ∀ b, μ.real {x | g<‖T (crossPart (A x) b)‖}≤p) :
    μ.real {x | 2*g+2*B*η<‖T (A x)‖}≤p/η := by
  classical
  let Bad : (J→Bool)→Set Ω := fun b => {x | g<‖T (crossPart (A x) b)‖}
  let I := fun b : J→Bool => (Bad b).indicator (fun _ => (1:ℝ))
  let F := fun x : Ω => ∑ b : J→Bool, I b x
  let C : ℝ := Fintype.card (J→Bool)
  letI : Nonempty (J→Bool) := ⟨fun _ => false⟩
  have Cp : 0<C := by dsimp [C]; exact_mod_cast Fintype.card_pos (α:=J→Bool)
  have It (b : J→Bool) : Integrable (I b) μ := (integrable_const _).indicator (badm b)
  have Ft : Integrable F μ := integrable_finsetSum _ (fun b _ => It b)
  have Fn : ∀ x, 0≤F x := fun x => Finset.sum_nonneg fun _ _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have Fe : (∫ x,F x ∂μ)≤C*p := by
    unfold F
    rw [integral_finsetSum _ (fun b _ => It b)]
    calc
      _ ≤ ∑ _ : J→Bool, p := by
        apply Finset.sum_le_sum
        intro b _
        unfold I
        rw [integral_indicator (badm b),integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
        exact badt b
      _ = _ := by simp [C,nsmul_eq_mul]
  let E := {x | 2*g+2*B*η<‖T (A x)‖}
  have sub : E ⊆ {x | C*η≤F x} := by
    intro x hx
    change 2*g+2*B*η<‖T (A x)‖ at hx
    have q (b : J→Bool) : ‖T (crossPart (A x) b)‖≤g+B*I b x := by
      by_cases u : x∈Bad b
      · have z := size x b
        simp only [I,indicator_of_mem u,mul_one]
        linarith only [z,g0]
      · have z : ‖T (crossPart (A x) b)‖≤g := le_of_not_gt u
        simpa [I,indicator_of_notMem u] using z
    have sum : (∑ b : J→Bool, ‖T (crossPart (A x) b)‖)≤C*g+B*F x := by
      have h := Finset.sum_le_sum (fun b (_:b∈(Finset.univ : Finset (J→Bool))) => q b)
      simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,C,F] using h
    have h := norm_cross_part_average T (A x) (diag x)
    have z := mul_le_mul_of_nonneg_left sum (by positivity : 0≤2/C)
    change ‖T (A x)‖≤(2/C)*(∑ b : J→Bool, ‖T (crossPart (A x) b)‖) at h
    change C*η≤F x
    by_contra! small
    have y : C*g+B*F x≤C*g+B*(C*η) := by gcongr
    have y' := mul_le_mul_of_nonneg_left y (by positivity : 0≤2/C)
    have id : (2/C)*(C*g+B*(C*η))=2*g+2*B*η := by field_simp <;> ring
    exact not_le_of_gt hx (h.trans (z.trans (y'.trans_eq id)))
  have mm := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ Fn) Ft (C*η)
  have mr : μ.real E≤μ.real {x | C*η≤F x} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono sub)
  change μ.real E≤p/η
  apply (le_div_iff₀ ηp).2
  have b := mul_le_mul_of_nonneg_left mr (mul_nonneg Cp.le ηp.le)
  have a := b.trans (mm.trans Fe)
  apply (le_of_mul_le_mul_left ?_ Cp)
  convert a using 1 <;> ring

#print axioms decoupled_norm_tail
end RobustFolkman.GeometricGap
