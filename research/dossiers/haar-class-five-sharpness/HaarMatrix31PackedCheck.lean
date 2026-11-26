import HaarMatrix31Packed
import Mathlib.Data.List.Sort

namespace HaarMatrix31PackedCheck
open HaarMatrix31Packed

theorem checker_sound (l : List ℕ) (h : strict l = true) : l.Pairwise (·<·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have hb : a<b ∧ strict (b::l)=true := by simpa [strict] using h
      have ht := ih hb.2
      apply List.pairwise_cons.mpr
      refine ⟨?_,ht⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb.1
      · exact hb.1.trans ((List.pairwise_cons.mp ht).1 x hx)

theorem census_sound (n : ℕ) (h : (census n).2=true) :
    (words zero true 3 n).Nodup := by
  let M := words zero true 3 n
  have hp := checker_sound (M.mergeSort (·≤·)) h
  have nd : (M.mergeSort (·≤·)).Nodup := hp.imp (fun lt => Nat.ne_of_lt lt)
  exact (List.mergeSort_perm M _).nodup_iff.mp nd

end HaarMatrix31PackedCheck

#print axioms HaarMatrix31PackedCheck.census_sound
