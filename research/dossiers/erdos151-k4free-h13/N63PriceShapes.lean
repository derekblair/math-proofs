import N63ChartChecker
namespace Erdos151N63
set_option maxHeartbeats 0
theorem price_3_3_3 : priceOK 9 3 3 3 := by unfold priceOK; decide +kernel
theorem price_4_2_3 : priceOK 9 4 2 3 := by unfold priceOK; decide +kernel
theorem price_4_3_2 : priceOK 9 4 3 2 := by unfold priceOK; decide +kernel
theorem price_4_3_3 : priceOK 9 4 3 3 := by unfold priceOK; decide +kernel
theorem price_4_4_1 : priceOK 9 4 4 1 := by unfold priceOK; decide +kernel
theorem price_4_4_2 : priceOK 9 4 4 2 := by unfold priceOK; decide +kernel
theorem price_4_4_3 : priceOK 9 4 4 3 := by unfold priceOK; decide +kernel
theorem price_5_3_2 : priceOK 9 5 3 2 := by unfold priceOK; decide +kernel
theorem price_5_4_1 : priceOK 9 5 4 1 := by unfold priceOK; decide +kernel
theorem price_5_4_2 : priceOK 9 5 4 2 := by unfold priceOK; decide +kernel
theorem price_5_5_1 : priceOK 9 5 5 1 := by unfold priceOK; decide +kernel
theorem price_5_5_2 : priceOK 9 5 5 2 := by unfold priceOK; decide +kernel
theorem price_6_3_1 : priceOK 9 6 3 1 := by unfold priceOK; decide +kernel
theorem price_6_4_1 : priceOK 9 6 4 1 := by unfold priceOK; decide +kernel
theorem price_6_5_1 : priceOK 9 6 5 1 := by unfold priceOK; decide +kernel
theorem price_6_6_1 : priceOK 9 6 6 1 := by unfold priceOK; decide +kernel
theorem price_7_7_0 : priceOK 9 7 7 0 := by unfold priceOK; decide +kernel
def nineShapes : List (Nat × Nat × Nat) := [(3, 3, 3), (4, 2, 3), (4, 3, 2), (4, 3, 3), (4, 4, 1), (4, 4, 2), (4, 4, 3), (5, 3, 2), (5, 4, 1), (5, 4, 2), (5, 5, 1), (5, 5, 2), (6, 3, 1), (6, 4, 1), (6, 5, 1), (6, 6, 1), (7, 7, 0)]
theorem nineShapes_sound (a b m : Nat) (h : (a,b,m) ∈ nineShapes) : priceOK 9 a b m := by
  simp only [nineShapes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> 
    injection h with ha hq <;> injection hq with hb hm <;> subst a <;> subst b <;> subst m <;>
    first | exact price_3_3_3 | exact price_4_2_3 | exact price_4_3_2 | exact price_4_3_3 | exact price_4_4_1 | exact price_4_4_2 | exact price_4_4_3 | exact price_5_3_2 | exact price_5_4_1 | exact price_5_4_2 | exact price_5_5_1 | exact price_5_5_2 | exact price_6_3_1 | exact price_6_4_1 | exact price_6_5_1 | exact price_6_6_1 | exact price_7_7_0
end Erdos151N63
