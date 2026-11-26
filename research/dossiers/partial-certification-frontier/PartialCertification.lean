import Lean.Elab.Tactic.Omega
namespace PartialCertification

/-- With no certified survivor, e counts certified outages and h-e certified corruptions.
The remaining opaque capacity must exceed its worst weighted faults. -/
theorem opaque_cut (k h f b : Nat) (hk : h ≤ k) :
    (∀ e : Nat, e ≤ f → e ≤ h → h - e ≤ b →
      f - e + 2 * (b - (h - e)) < k - h) ↔
    k + (h - f) ≥ f + 2 * b + 1 := by
  constructor
  · intro hgood
    by_cases hn : h ≤ f + b
    · by_cases hl : h ≤ f
      · specialize hgood h (by omega) (by omega) (by omega)
        omega
      · specialize hgood f (by omega) (by omega) (by omega)
        omega
    · omega
  · intro he e hef heh heb
    omega

/-- If weighted opaque faults can meet the available surviving capacity,
an identical view divides its surviving positions between two distinct values. -/
theorem ambiguous_split (n b : Nat) (h : n ≤ 2*b) :
    ∃ a d : Nat, a + d = n ∧ a ≤ b ∧ d ≤ b := by
  by_cases hn : n ≤ b
  · exact ⟨n,0,by omega,hn,Nat.zero_le _⟩
  · exact ⟨b,n-b,by omega,by omega,by omega⟩

/-- At minimum feasible length and b>0, exactly all but one copy need certification. -/
theorem at_shortest (h f b : Nat) (hb : 0 < b) :
    f + b + 1 + (h - f) ≥ f + 2*b + 1 ↔ f + b ≤ h := by
  omega

/-- Once fewer than K verified points survive, the ideal frontier bounds
all actual RS errors and erasures. -/
theorem rs_decoding_budget (n K h f b z err : Nat)
    (hK : 0 < K) (hKn : K ≤ n)
    (frontier : n - K + 1 + ((h - (K - 1)) - f) ≥ f + 2 * b + 1)
    (hmin : h - (K - 1) ≤ z) (budget : err + (z-f) ≤ b) :
    z + 2 * err ≤ n - K := by omega

#print axioms rs_decoding_budget
#print axioms opaque_cut
#print axioms ambiguous_split
#print axioms at_shortest
end PartialCertification
