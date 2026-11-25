import DelayRestrict

namespace CoverCutoff

def AltRows {α : Type} [LT α] (r : ℕ→α) (h j : ℕ) : Prop :=
  Ascending (localA r) 0 (h+j) ∧
  Ascending (localC r) 0 (h+j-1) ∧
  Ascending (localB r) 0 (h-1) ∧
  localB r (h-2) < localA r 0 ∧
  ∀ t, t < j →
    localA r t < localB r (t+h-1) ∧
    localB r (t+h-1) < localA r (t+1) ∧
    localA r (t+h) < localC r t

theorem altRows_iff_global {α : Type} [Preorder α] {r : ℕ→α} {h j : ℕ}
    (hh : 2≤h) (hj : 1≤j) : AltRows r h j ↔ GlobalRows r h j := by
  constructor
  · rintro ⟨ha,hc,hB,hB0,hT⟩
    refine ⟨ha,?_,hc,?_⟩
    · intro i _ hi
      by_cases hf : i+1<h-1
      · exact hB i (by omega) (by omega)
      by_cases he : i=h-2
      · have hx : i+1=0+h-1 := by omega
        rw [hx,he]
        exact hB0.trans (hT 0 (by omega)).1
      · let t := i-(h-1)
        have ht : t<j := by dsimp [t]; omega
        have ht' : t+1<j := by dsimp [t]; omega
        have e1 : i=t+h-1 := by dsimp [t]; omega
        have e2 : i+1=(t+1)+h-1 := by omega
        rw [e2,e1]
        exact (hT t ht).2.1.trans (hT (t+1) ht').1
    · intro t ht
      refine ⟨?_,hT t ht⟩
      by_cases h0 : t=0
      · simpa [h0] using hB0
      · have he : t+h-2=(t-1)+h-1 := by omega
        have hf : t=t-1+1 := by omega
        rw [he]
        exact (hT (t-1) (by omega)).2.1.trans_eq (congrArg (localA r) hf.symm)
  · rintro ⟨ha,hb,hc,hT⟩
    refine ⟨ha,hc,fun i h1 h2 => hb i h1 (by omega),?_,fun t ht => (hT t ht).2⟩
    simpa using (hT 0 (by omega)).1

#print axioms altRows_iff_global
end CoverCutoff
