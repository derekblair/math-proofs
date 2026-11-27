import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SparseHalfThreeHeavy

/-- If three blocks have small-side mass at least one (scaled by ten),
two of the blocks already have all the capacity required after taking
the larger sides and the isolate mass. Their second price suffices. -/
theorem two_prices (a h p : ℝ) (ha1 : 19/5≤a) (ha2 : a≤4)
    (hh : 0≤h) (hh' : h≤4-a) (hp : 0≤p)
    (hp1 : p≤1+h) (hp2 : p≤1+(4-a-h)/2) :
    p*((a-h)/2)≤2 := by
  let d := 4-a
  have hd : 0≤d := by dsimp [d]; linarith
  have hdl : d≤1/5 := by dsimp [d]; linarith
  have hhd : h≤d := hh'
  have hneed : 0≤(a-h)/2 := by dsimp [d] at hhd; linarith
  have h1 := mul_le_mul_of_nonneg_right hp1 hneed
  have h2 := mul_le_mul_of_nonneg_right hp2 hneed
  by_cases hh0 : h≤d/3
  · have hM := mul_nonneg (show 0≤d/3-h by linarith)
      (show 0≤3-d-d/3-h by linarith)
    dsimp [d] at hM
    nlinarith [sq_nonneg (4-a)]
  · have hM := mul_nonneg (show 0≤h-d/3 by linarith)
      (show 0≤6-d/3-h by linarith)
    dsimp [d] at hM
    nlinarith [sq_nonneg (4-a)]

#print axioms two_prices
end SparseHalfThreeHeavy
