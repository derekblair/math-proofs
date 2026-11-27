import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfFractionalCaseTwo
open scoped BigOperators
variable {V : Type*}

variable (A D : Finset V) (m f : V → ℝ) (W : V → V → ℝ)

noncomputable def da (x : V) : ℝ := ∑ v ∈ A, m v * W v x
noncomputable def gap (x : V) : ℝ := 1/5-da A m W x
noncomputable def load (v : V) : ℝ := ∑ x ∈ D, f x * W v x
noncomputable def rem (v : V) : ℝ := 1/10-load D f W v
noncomputable def z : ℝ := ∑ x ∈ D, f x * gap A m W x
noncomputable def r (v : V) : ℝ := ∑ x ∈ D, f x * W v x * gap A m W x

/-- The first deficit-identity requires no rationality or size assumptions. -/
theorem rem_sum (ha : (∑ v ∈ A, m v)=2/5) (hd : (∑ x ∈ D, f x)=1/5) :
    (∑ v ∈ A, m v * rem D f W v)=z A D m f W := by
  have hf : (∑ v ∈ A, m v * load D f W v) =
      ∑ x ∈ D, f x * da A m W x := by
    simp only [load, da, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold rem z gap
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [ha,hd,hf]
  ring

/-- Exact finite-double-counting second moment, a weighted analogue of Fubini. -/
theorem r_sum :
    (∑ v ∈ A, m v * r A D m f W v) =
      (1/5)*z A D m f W - ∑ x ∈ D, f x * (gap A m W x)^2 := by
  unfold r z
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ v ∈ A, m v * (f x * W v x * gap A m W x)) =
      (∑ v ∈ A, m v * W v x) * f x * gap A m W x := by
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = (1/5)*(f x*gap A m W x)-f x*(gap A m W x)^2 := by
        unfold gap da
        ring

theorem average_strict (β : ℝ)
    (ha : (∑ v ∈ A, m v)=2/5) (hd : (∑ x ∈ D, f x)=1/5)
    (hm : ∀ v ∈ A, 0≤m v)
    (hf : ∀ x ∈ D, 0≤f x)
    (hg : ∀ x ∈ D, 0≤gap A m W x ∧ gap A m W x≤1/10)
    (hz : 0<z A D m f W)
    (hbound : ∀ v ∈ A, β - 1/50 ≤
      rem D f W v/10 - (3/4)*(rem D f W v)^2 - r A D m f W v) :
    β < 1/50 := by
  have hh := rem_sum A D m f W ha hd
  have hr := r_sum A D m f W
  have h2 : (∑ x ∈ D, f x*(gap A m W x)^2) ≤ z A D m f W/10 := by
    unfold z
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x hx
    have hp := mul_nonneg (hg x hx).1 (sub_nonneg.mpr (hg x hx).2)
    have hm0 := mul_nonneg (hf x hx) hp
    nlinarith only [hm0]
  let P := ∑ v ∈ A, m v * (rem D f W v)^2
  have hsq : 0 ≤ (∑ v ∈ A, m v*(rem D f W v - (5/2)*z A D m f W)^2) := by
    exact Finset.sum_nonneg (fun v hv => mul_nonneg (hm v hv) (sq_nonneg _))
  have heq : (∑ v ∈ A, m v*(rem D f W v - (5/2)*z A D m f W)^2) =
      P - (5/2)*(z A D m f W)^2 := by
    unfold P
    have he : (∑ v ∈ A, m v*(rem D f W v - (5/2)*z A D m f W)^2) =
        ∑ v ∈ A, (m v*(rem D f W v)^2 -
          (m v*rem D f W v)*(5*z A D m f W) +
          m v*((5/2)*z A D m f W)^2) := by
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [he]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [ha,hh]
    ring
  rw [heq] at hsq
  have hP : 0<P := by
    have hn : 0<(z A D m f W)^2 := by positivity
    linarith
  have hb := Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hbound v hv) (hm v hv))
  have hb' : (2/5)*(β-1/50) ≤ z A D m f W/10 - (3/4)*P -
       (∑ v ∈ A, m v * r A D m f W v) := by
    have he : (∑ v ∈ A, m v *
      (rem D f W v / 10 - 3 / 4 * (rem D f W v)^2 - r A D m f W v)) =
       (∑ v ∈ A, ((m v * rem D f W v)/10 -
         (3/4)*(m v * (rem D f W v)^2) - m v * r A D m f W v)) := by
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [he, ← Finset.sum_mul,ha] at hb
    have ht : (∑ v ∈ A, (m v * rem D f W v)/10) = z A D m f W/10 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [hh]
    have ht₂ : (∑ v ∈ A, (3/4)*(m v * (rem D f W v)^2)) = (3/4)*P := by
      dsimp [P]
      rw [Finset.mul_sum]
    simpa only [Finset.sum_sub_distrib, ht, ht₂] using hb
  rw [hr] at hb'
  linarith

#print axioms average_strict
end SparseHalfFractionalCaseTwo
