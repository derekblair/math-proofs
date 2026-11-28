import NestedFirst00
import NestedFirst01
import NestedFirst02
import NestedFirst03
import NestedFirst04
import NestedFirst05
import NestedFirst06
import NestedFirst07
import NestedFirst08
import NestedFirst09
import NestedFirst10
import NestedFirst11
import NestedFirst12
import NestedFirst13
import NestedTwoModeBound
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace NestedExposure

private theorem perm_sum {a b : List Nat} (h : a.Perm b) : a.sum=b.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih jh => exact ih.trans jh

theorem exact_scan_asym (s : Fin 14) :
    fastScan (asymAccept s.val) 9 (63-s.val) 0 Moments.empty=true := by
  fin_cases s
  · exact nested_asym_00
  · exact nested_asym_01
  · exact nested_asym_02
  · exact nested_asym_03
  · exact nested_asym_04
  · exact nested_asym_05
  · exact nested_asym_06
  · exact nested_asym_07
  · exact nested_asym_08
  · exact nested_asym_09
  · exact nested_asym_10
  · exact nested_asym_11
  · exact nested_asym_12
  · exact nested_asym_13
/-- The full labelled exact-63 exposure bound, not just the two
attaining count vectors. -/
theorem exact_padded_asym_probability (s : Nat) (hs : s≤13)
    (l : List Nat) (len : l.length=9) (total : s+l.sum=63) (cap : ∀ x∈l, x≤13) :
    pStar≤modeProb s (moments l) qStar := by
  let sort := l.mergeSort (fun x y=>decide (x≤y))
  have per : sort.Perm l := List.mergeSort_perm _ _
  have sorted : sort.Pairwise (·≤·) := List.pairwise_mergeSort' _ l
  have first : fastScan (asymAccept s) 9 (63-s) 0 Moments.empty=true :=
    exact_scan_asym ⟨s,by omega⟩
  have verify : fastScan (asymAccept s) sort.length sort.sum 0 Moments.empty=true := by
    rw [per.length_eq,len,perm_sum per,show l.sum=63-s by omega]
    exact first
  have good := fast_scan_sound (asymAccept s) sort 0 Moments.empty sorted (fun _ _=>Nat.zero_le _)
    (fun x hx=>cap x (per.mem_iff.mp hx)) verify
  change asymAccept s (moments sort)=true at good
  rw [moments_perm sort l per] at good
  exact accepted_score_prob_at_least s (moments l) good

#print axioms exact_padded_asym_probability
end NestedExposure
