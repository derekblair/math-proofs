import GapEquiv
namespace CoverCutoff

/-- At the first distinction the larger packing count exceeds the smaller by
the h-th Catalan number, even with equal length and equal overlap. -/
theorem equal_width_exact_delay {h : ℕ} (hh : 2≤h) :
    ∃ p q : Equiv.Perm (Fin (3*h+1)), Admissible p 3 ∧ Admissible q 3 ∧
      (∀ j, 1≤j → j≤h → packCount p 3 j = packCount q 3 j) ∧
      packCount q 3 (h+1) = packCount p 3 (h+1) + catalan h := by
  refine ⟨equalWidthPeer h (by omega), delayed h hh, peer_admissible hh, delayed_admissible hh, ?_, ?_⟩
  · intro j hj hlim
    exact (peer_count hh hj).trans (same_counts_below hh hj hlim)
  · rw [peer_count hh (by omega)]
    exact exact_delayed_difference hh

#print axioms equal_width_exact_delay
end CoverCutoff
