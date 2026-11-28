import NestedExposureCore

namespace NestedExposure

private theorem perm_sum {a b : List Nat} (h : a.Perm b) : a.sum=b.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih jh => exact ih.trans jh

/-- Numeric results on sorted rows cover all labelled exposure count vectors. -/
theorem scan_sound_unsorted (accept : Moments → Bool) (l : List Nat)
    (upper : ∀ x∈l, x≤13)
    (h : scan accept l.length l.sum 0 Moments.empty=true) :
    accept (moments l)=true := by
  let sort := l.mergeSort (fun x y => decide (x≤y))
  have per : sort.Perm l := List.mergeSort_perm _ _
  have inc : sort.Pairwise (·≤·) := List.pairwise_mergeSort' _ l
  have hs : scan accept sort.length sort.sum 0 Moments.empty=true := by
    rwa [per.length_eq,perm_sum per]
  have hu (x : Nat) (hx : x∈sort) : x≤13 := upper x (per.mem_iff.mp hx)
  have ans := scan_sound accept sort 0 Moments.empty inc (fun _ _=>Nat.zero_le _) hu hs
  change accept (moments sort)=true at ans
  rwa [moments_perm sort l per] at ans

#print axioms scan_sound_unsorted
end NestedExposure
