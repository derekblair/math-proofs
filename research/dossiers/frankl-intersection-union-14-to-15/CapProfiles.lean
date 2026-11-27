import EliminateDom

namespace IU.Eliminate

theorem rank_succ' (a t : Nat) :
    rank a (t+1) = rank a t + (if a.testBit t then 1 else 0) := by
  unfold rank
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : a.testBit t
  · simp [h]
  · simp [h]

theorem rank_le_length (a t : Nat) : rank a t ≤ t := by
  simpa [rank] using List.length_filter_le (p:=fun i => a.testBit i) (List.range t)

theorem rank_step_le (a b t : Nat) : rank a t ≤ rank a b + (t-b) := by
  by_cases h : b≤t
  · obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le h
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Nat.add_succ,rank_succ']
      split <;> omega
  · have mono (v : Nat) : rank a v ≤ rank a (v+1) := by rw [rank_succ']; omega
    have le : rank a t ≤ rank a b := monotone_nat_of_le_succ mono (by omega)
    omega

theorem rank_monotone (a : Nat) : Monotone (rank a) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [rank_succ']
  omega

/-- Rank envelope for the greedy earliest profile with a cap of c in the first b positions. -/
def envelope (k b c t : Nat) : Nat := min t (min k (c + (t-b)))

theorem cap_envelope {a k n b c : Nat} (count : rank a n = k) (cap : rank a b ≤ c)
    {t : Nat} (tn : t≤n) : rank a t ≤ envelope k b c t := by
  unfold envelope
  apply le_min (rank_le_length a t)
  apply le_min
  · exact count ▸ rank_monotone a tn
  · exact (rank_step_le a b t).trans (Nat.add_le_add_right cap _)

theorem cap_domination {a u k n b c : Nat} (count : rank a n = k) (cap : rank a b ≤ c)
    (full : rank u n = k)
    (exactGreedy : ∀ t ∈ List.range (n+1), rank u t = envelope k b c t) :
    Dominates n u a := by
  refine ⟨count.trans full.symm, ?_⟩
  intro t ht
  rw [exactGreedy t ht]
  exact cap_envelope count cap (by have := List.mem_range.mp ht; omega)

/-- For two even anchor blocks with one free position, the union of the two
    outsider reasons collapses to one prefix cap in each cardinality layer. -/
theorem outsider_cap {a n l r k : Nat} (kn : rank a n=k) (hn : n=2*l+1+2*r) :
    (rank a (2*l) ≤ l ∨ r ≤ k - rank a (2*l+1)) ↔
      (if k≤l+r then rank a (2*l) ≤ l else rank a (2*l+1) ≤ k-r) := by
  have rb : rank a (2*l) ≤ rank a (2*l+1) :=
    rank_monotone a (by omega)
  have rt : rank a (2*l+1) ≤ k := kn ▸ rank_monotone a (by omega)
  have step : rank a (2*l+1) ≤ rank a (2*l)+1 := by
    simpa using rank_step_le a (2*l) (2*l+1)
  split
  · rename_i small
    constructor
    · rintro (L|R)
      · exact L
      · by_cases Rr : r=0
        · omega
        · omega
    · intro L
      exact Or.inl L
  · rename_i big
    constructor
    · rintro (L|R) <;> omega
    · intro R
      exact Or.inr (by omega)

#print axioms outsider_cap
#print axioms cap_domination
end IU.Eliminate
