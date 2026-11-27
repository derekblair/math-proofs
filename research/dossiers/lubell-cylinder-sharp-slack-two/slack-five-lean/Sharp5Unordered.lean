import Sharp5Conclusion
import RawComplement

namespace IU.Sharp5
open IU.Slack

/-- Raw Lubell optimum at excess five, in either parameter order.
The optimum's two explicit profile masks are checked, not assumed. -/
theorem sharp_five {t u : Nat} (ht : 0<t) (hu : 0<u) (h2 : 2≤max t u) :
    let best := optimum (min t u) (max t u)
    (∃ F : IU.Sys, IU.IsIU F (t+u+5) t u ∧ rawSum (t+u+5) F=best) ∧
    ∀ F : IU.Sys, IU.IsIU F (t+u+5) t u → rawSum (t+u+5) F≤best := by
  dsimp only
  by_cases h : t≤u
  · simp only [min_eq_left h,max_eq_right h] at *
    exact sharp_five_ordered ht h2 h
  · have k : u≤t := by omega
    simp only [min_eq_right k,max_eq_left k] at *
    obtain ⟨⟨F,fok,fs⟩,cap⟩ := sharp_five_ordered hu h2 k
    rw [Nat.add_comm u t] at fok fs cap
    constructor
    · exact ⟨complement F (t+u+5),flip_valid fok (by omega),by rwa [raw_flip fok]⟩
    · intro A aok
      rw [←raw_flip aok]
      exact cap _ (flip_valid aok (by omega))

#print axioms sharp_five
end IU.Sharp5
