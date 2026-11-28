import NestedExposureCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Field.Rat

namespace NestedExposure

def qStar : ℚ := 5077873 / 9816373
def pStar : ℚ := 106948625 / 24647510264
def meanCount (q : ℚ) : ℚ := 8-q

/-- Common denominator 4663897056 for both coordinate probabilities. -/
def modeProb (s : Nat) (m : Moments) (q : ℚ) : ℚ :=
  ((1-q)*(m.e4 : ℚ) + q*9*((13-s : Nat) : ℚ)*(m.e3 : ℚ)) / 4663897056

def exposureA : List Nat := List.replicate 9 7
def exposureB : List Nat := List.replicate 4 5 ++ List.replicate 5 6

theorem witnessA_forms :
    exposureA.length=9 ∧ exposureA.sum=63 ∧
    (moments exposureA).e4=6378750 ∧
    9*13*(moments exposureA).e3=33169500 := by decide

theorem witnessB_forms :
    exposureB.length=9 ∧ exposureB.sum=50 ∧
    (moments exposureB).e4=41923861 := by decide

private theorem a_form (q : ℚ) :
    modeProb 0 (moments exposureA) q = ((1-q)*6378750 + q*33169500)/4663897056 := by
  unfold modeProb
  rw [witnessA_forms.2.2.1]
  have a := witnessA_forms.2.2.2
  change 117*(moments exposureA).e3=33169500 at a
  have h : (moments exposureA).e3=283500 := by omega
  rw [h]
  norm_num
  ring

private theorem b_form (q : ℚ) :
    modeProb 13 (moments exposureB) q = ((1-q)*41923861)/4663897056 := by
  unfold modeProb
  rw [witnessB_forms.2.2]
  norm_num

theorem both_active_cross :
    modeProb 0 (moments exposureA) qStar=pStar ∧
    modeProb 13 (moments exposureB) qStar=pStar := by
  rw [a_form,b_form]
  norm_num [qStar,pStar]

/-- Neither active exposure needs to be the minimizer away from the
optimum. Their minimum still upper bounds the full minimum for every mode
weight, so this exact inequality certifies the matching upper bound. -/
theorem two_active_ratio_upper (q : ℚ) (qh : q≤1) :
    min (modeProb 0 (moments exposureA) q) (modeProb 13 (moments exposureB) q) / meanCount q ≤
    pStar / meanCount qStar := by
  have h1 : 0 < meanCount q := by unfold meanCount; linarith
  have h2 : 0 < meanCount qStar := by norm_num [meanCount,qStar]
  apply (div_le_div_iff₀ h1 h2).2
  by_cases hq : q≤qStar
  · apply (mul_le_mul_of_nonneg_right (min_le_left _ _) h2.le).trans
    rw [a_form]
    unfold meanCount qStar pStar at *
    linarith
  · apply (mul_le_mul_of_nonneg_right (min_le_right _ _) h2.le).trans
    rw [b_form]
    unfold meanCount qStar pStar at *
    linarith

theorem exact_score_matches (s : Nat) (m : Moments) :
    modeProb s m qStar = (asymNum s m : ℚ) / (4663897056*9816373) := by
  unfold modeProb qStar asymNum
  push_cast
  ring

theorem accepted_score_prob_at_least (s : Nat) (m : Moments) (h : asymAccept s m = true) :
    pStar≤modeProb s m qStar := by
  have z : 198656215348500 ≤ asymNum s m := of_decide_eq_true h
  rw [exact_score_matches]
  unfold pStar
  have c : (198656215348500:ℚ) ≤ (asymNum s m : ℚ) := by exact_mod_cast z
  exact (show (106948625:ℚ)/24647510264 = 198656215348500/(4663897056*9816373) by norm_num).le.trans
    (div_le_div_of_nonneg_right c (by norm_num))

theorem exact_two_family_multiplier :
    4*meanCount qStar/pStar = (5164047515744:ℚ)/748640375 := by norm_num [meanCount,qStar,pStar]

#print axioms two_active_ratio_upper
#print axioms accepted_score_prob_at_least
#print axioms exact_two_family_multiplier
end NestedExposure
