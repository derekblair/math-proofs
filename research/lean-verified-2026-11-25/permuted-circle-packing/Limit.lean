import Cardinal
import Mathlib.Topology.Algebra.Order.Field

namespace PermCircles

open Filter Real
open scoped Topology

lemma inverse_square_top :
    Tendsto (fun x : ℝ => 1/x^2) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).pow 2
  simpa [one_div,inv_pow] using h

lemma norm_order_limit {n : ℝ → ℝ} {L A B C : ℝ}
    (hlo : ∀ᶠ r in atTop, L*r^2-C*r ≤ n r)
    (hhi : ∀ᶠ r in atTop, n r ≤ L*r^2+A*r+B) :
    Tendsto (fun r => n r/r^2) atTop (𝓝 L) := by
  have hinv := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hl : Tendsto (fun r : ℝ => L-C*r⁻¹) atTop (𝓝 L) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  have hh : Tendsto (fun r : ℝ => L+A*r⁻¹+B*(1/r^2)) atTop (𝓝 L) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add
      (tendsto_const_nhds.mul inverse_square_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
  · filter_upwards [hlo,eventually_ge_atTop (1:ℝ)] with r hr rp
    have h0 : 0 < r := by linarith
    apply (le_div_iff₀ (pow_pos h0 2)).2
    convert hr using 1
    field_simp [h0.ne']
  · filter_upwards [hhi,eventually_ge_atTop (1:ℝ)] with r hr rp
    have h0 : 0 < r := by linarith
    apply (div_le_iff₀ (pow_pos h0 2)).2
    convert hr using 1
    field_simp [h0.ne']

/-- Analytic squeeze for the clipped-area density. The lower estimate permits
    O(r) boundary disks, and applies uniformly over all choices of minimizers. -/
lemma clipped_density_limit {n density : ℝ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (hn : Tendsto (fun r => n r/r^2) atTop (𝓝 L))
    {E F : ℝ}
    (hlo : ∀ᶠ r in atTop, π*r^2*(n r-E*r-F)/(n r-1)^2 ≤ density r)
    (hhi : ∀ᶠ r in atTop, density r ≤ π*r^2*n r/(n r-1)^2) :
    Tendsto density atTop (𝓝 (π/L)) := by
  have hinv := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hd : Tendsto (fun r => (n r-1)/r^2) atTop (𝓝 L) := by
    have hh := hn.sub inverse_square_top
    simpa [sub_div] using hh
  have hnlo : Tendsto (fun r => n r/r^2-E*r⁻¹-F*(1/r^2)) atTop (𝓝 L) := by
    simpa using (hn.sub (tendsto_const_nhds.mul hinv)).sub
      (tendsto_const_nhds.mul inverse_square_top)
  have hs : π*L/L^2 = π/L := by field_simp
  have hnon : L^2 ≠ 0 := pow_ne_zero _ hL
  have hp : Tendsto (fun _ : ℝ => π) atTop (𝓝 π) := tendsto_const_nhds
  have hl := (hp.mul hnlo).div (hd.pow 2) hnon
  have hh := (hp.mul hn).div (hd.pow 2) hnon
  rw [hs] at hl hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
  · filter_upwards [hlo,eventually_ge_atTop (1:ℝ)] with r hr rp
    have h0 : 0 < r := by linarith
    convert hr using 1
    simp only [Pi.div_apply]
    by_cases hc : n r-1=0
    · simp [hc]
    · field_simp [h0.ne',hc]
  · filter_upwards [hhi,eventually_ge_atTop (1:ℝ)] with r hr rp
    have h0 : 0 < r := by linarith
    convert hr using 1
    simp only [Pi.div_apply]
    by_cases hc : n r-1=0
    · simp [hc]
    · field_simp [h0.ne',hc]

#print axioms norm_order_limit
#print axioms clipped_density_limit
end PermCircles
