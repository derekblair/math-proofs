import GreedyLocalHalf
import GraphonCaseTwoMarginals
import GreedyScalar

open Set MeasureTheory Function
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

noncomputable def greedyLocalPoly (b x : ℝ) :=
  (1/4)*(1/2-b-x)*(1/2+b+3*x)

lemma greedy_poly_tangent (b m x : ℝ) :
    greedyLocalPoly b x ≤ greedyLocalPoly b m +
      ((1/4)-b-(3/2)*m)*(x-m) := by
  unfold greedyLocalPoly
  nlinarith only [sq_nonneg (x-m)]

/-- Averaging the actual local estimates only needs the two Fubini
identities and the moment upper bound; the concave part is replaced by
its value at the true mean. -/
theorem greedy_average (A b c opt : ℝ) (hb : 0<b) (hm : mass ν=b)
    (E R : X→ℝ) (hE : BMeas E) (hR : BMeas R)
    (he : (∫ v,E v ∂ν)=c/2)
    (hRsum : (∫ v,R v ∂ν)≤(1/2-A+b/2)*c/2-(b/2)*(1/2-A)*(1-A-b))
    (hlocal : ∀ᵐ v ∂ν, opt ≤ (1/2-A)*(b-A)+R v+greedyLocalPoly b (E v)) :
    opt≤greedyCaseTwo A b c := by
  let m := c/(2*b)
  let slope := (1/4)-b-(3/2)*m
  let C := (1/2-A)*(b-A) + greedyLocalPoly b m
  have bD : BMeas (fun v=>E v-m) := hE.sub (BMeas.const m)
  have hI : Integrable (fun v=>C+R v+slope*(E v-m)) ν :=
    (integrable_const C).add (bMeas_integrable ν hR) |>.add ((bMeas_integrable ν bD).const_mul slope)
  have hh : ∀ᵐ v ∂ν, opt ≤ C+R v+slope*(E v-m) := by
    filter_upwards [hlocal] with v hv
    have ht := greedy_poly_tangent b m (E v)
    dsimp [C,slope]
    linarith
  have h := integral_mono_ae (integrable_const opt) hI hh
  have hCR : Integrable (fun v=>C+R v) ν := (integrable_const C).add (bMeas_integrable ν hR)
  rw [integral_add hCR ((bMeas_integrable ν bD).const_mul slope),
    integral_add (integrable_const C) (bMeas_integrable ν hR),integral_const_mul,
    integral_sub (bMeas_integrable ν hE) (integrable_const m),integral_const,
    integral_const,integral_const,smul_eq_mul,smul_eq_mul,smul_eq_mul] at h
  change mass ν*opt ≤ mass ν*C+(∫ v,R v ∂ν)+slope*((∫ v,E v ∂ν)-mass ν*m) at h
  rw [hm,he] at h
  have eq : b*m=c/2 := by dsimp [m]; field_simp
  rw [eq,sub_self,mul_zero,add_zero] at h
  have hh : opt ≤ C + ((1/2-A+b/2)*c/2-(b/2)*(1/2-A)*(1-A-b))/b := by
    have hd : ((1/2-A+b/2)*c/2-(b/2)*(1/2-A)*(1-A-b))/b*b = _ := div_mul_cancel₀ _ hb.ne'
    by_contra! hn
    have hw := mul_lt_mul_of_pos_right hn hb
    nlinarith only [h,hRsum,hw,hd]
  exact hh

#print axioms greedy_average
end SparseHalfGraphon
