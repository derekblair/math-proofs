import LowSmallSide

namespace SparseHalfOneHeavyNormalized
open SparseHalfLowSmallSide

noncomputable def base (θ u : ℝ) : ℝ :=
  if 8-2*u≤θ+1 then g (8-2*u) else θ+g (7-2*u-θ)

/-- Worst normalized case for one over-cap small-side block.
u is its total mass and θ is the last marginal price. -/
theorem main (θ u : ℝ) (hθ : 1≤θ) (hθ' : θ≤2) (hu : 2≤u) (hu' : u≤4) :
    min (u^2/4) (θ*u/2)+base θ u-θ≤2 := by
  unfold base
  by_cases h : 8-2*u≤θ+1
  · rw [if_pos h]
    by_cases hu3 : 3≤u
    · rw [eq_small _ (by linarith : 8-2*u≤2)]
      have hm := min_le_right (u^2/4) (θ*u/2)
      have hz := mul_nonneg (show 0≤u/2-1 by linarith) (show 0≤2-θ by linarith)
      have hf := mul_nonneg (show 0≤u-3 by linarith) (show 0≤4-u by linarith)
      nlinarith
    · rw [eq_large _ (by linarith : 2≤8-2*u)]
      by_cases ha : u≤14/5
      · have hm := min_le_left (u^2/4) (θ*u/2)
        have hsq := mul_nonneg (show 0≤14/5-u by linarith) (show 0≤14/5+u by linarith)
        nlinarith
      · have hmon : min (u^2/4) (θ*u/2) - θ≤u^2/4-u/2 := by
          by_cases hj : u/2≤θ
          · have hh := min_le_left (u^2/4) (θ*u/2); linarith
          · have hh := min_le_right (u^2/4) (θ*u/2)
            have hp := mul_nonneg (show 0≤u/2-θ by linarith) (show 0≤u/2-1 by linarith)
            nlinarith
        have hp := mul_nonneg (show 0≤u-14/5 by linarith) (show 0≤3-u by linarith)
        nlinarith
  · rw [if_neg h, eq_small _ (by linarith : 7-2*u-θ≤2)]
    have hu3 : u≤3 := by linarith
    let L := 7-2*u
    have hLt : θ≤L := by dsimp [L]; linarith
    have hL1 : 1≤L := hθ.trans hLt
    have hF1 : 1*u/2+(L-1)^2/4≤2 := by
      dsimp [L]
      have hp := mul_nonneg (show 0≤u-2 by linarith) (show 0≤3-u by linarith)
      nlinarith
    have hFu (huL : u/2≤L) : u^2/4+(L-u/2)^2/4≤2 := by
      have h2 : u≤14/5 := by dsimp [L] at huL; linarith
      have hp := mul_nonneg (show 0≤u-2 by linarith) (show 0≤14/5-u by linarith)
      dsimp [L]
      nlinarith
    by_cases ho : u/2≤θ
    · have hm := min_le_left (u^2/4) (θ*u/2)
      have hp := mul_nonneg (show 0≤θ-u/2 by linarith) (show 0≤2*L-u/2-θ by linarith)
      change min (u^2/4) (θ*u/2)+(θ+(L-θ)^2/4)-θ≤2
      nlinarith [hFu (ho.trans hLt)]
    · let b := min (u/2) L
      have hb : θ≤b := le_min (by linarith) hLt
      have hb1 : 1≤b := hθ.trans hb
      have hFb : b*u/2+(L-b)^2/4≤2 := by
        by_cases hj : u/2≤L
        · dsimp [b]
          rw [min_eq_left hj]
          nlinarith [hFu hj]
        · have hL' : L≤u/2 := by linarith
          have huL : 14/5≤u := by dsimp [L] at hL'; linarith
          have hp := mul_nonneg (show 0≤u-14/5 by linarith) (show 0≤2*u-7/5 by linarith)
          dsimp [b]
          rw [min_eq_right hL']
          dsimp [L]
          nlinarith
      have hh := mul_nonneg (show 0≤θ-1 by linarith) (show 0≤b-θ by linarith)
      have h1 := mul_nonneg (show 0≤b-θ by linarith) (show 0≤2-(1*u/2+(L-1)^2/4) by linarith)
      have h2 := mul_nonneg (show 0≤θ-1 by linarith) (show 0≤2-(b*u/2+(L-b)^2/4) by linarith)
      have hmul := mul_nonneg (show 0≤b-1 by linarith) hh
      have hprod : 0≤(b-1)*(2-(θ*u/2+(L-θ)^2/4)) := by
        linear_combination h1+h2+1/4*hmul
      have hval : θ*u/2+(L-θ)^2/4≤2 := by
        by_cases he : b=1
        · have hθ1 : θ=1 := by linarith
          rw [hθ1]
          exact hF1
        · exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod (sub_pos.mpr (lt_of_le_of_ne hb1 (Ne.symm he))))
      have hm := min_le_right (u^2/4) (θ*u/2)
      change min (u^2/4) (θ*u/2)+(θ+(L-θ)^2/4)-θ≤2
      linarith

#print axioms main
end SparseHalfOneHeavyNormalized
