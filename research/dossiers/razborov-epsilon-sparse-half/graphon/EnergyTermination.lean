import WeakRegularityStep

namespace SparseHalfGraphon

/-- Generic finite termination with an explicit branching bound and a
transitive refinement witness. In weak regularity δ=ε² and branching ≤4. -/
theorem energy_termination_aux {P : Type*} (E:P→ℝ) (size:P→ℕ) (Good:P→Prop)
    (R:P→P→Prop) (refl : ∀ p, R p p) (trans : ∀ {p q r}, R p q→R q r→R p r)
    (δ:ℝ) (hδ:0<δ) (hi : ∀ p, E p≤1)
    (hs : ∀ p, ¬Good p → ∃ q, R p q ∧ E p+δ<E q ∧ size q≤size p*4)
    (n:ℕ) (p:P) (hp : 1-E p<((n:ℝ)+1)*δ) :
    ∃ q, Good q ∧ R p q ∧ size q≤size p*4^n := by
  induction n generalizing p with
  | zero =>
    by_cases h : Good p
    · exact ⟨p,h,refl p,by simp⟩
    · obtain ⟨q,_,hQ,_⟩ := hs p h
      have ht := hi q
      norm_num at hp
      linarith
  | succ n ih =>
    by_cases h : Good p
    · exact ⟨p,h,refl p,Nat.le_mul_of_pos_right _ (by positivity)⟩
    · obtain ⟨q,hpq,hQ,hsize⟩ := hs p h
      have hsmall : 1-E q<((n:ℝ)+1)*δ := by
        rw [Nat.cast_succ] at hp
        nlinarith
      obtain ⟨r,hGood,hqr,hr⟩ := ih q hsmall
      refine ⟨r,hGood,trans hpq hqr,?_⟩
      calc
        size r ≤ size q*4^n := hr
        _ ≤ (size p*4)*4^n := Nat.mul_le_mul_right _ hsize
        _ = size p*4^(n+1) := by rw [pow_succ]; ac_rfl

theorem energy_termination {P : Type*} (E:P→ℝ) (size:P→ℕ) (Good:P→Prop)
    (R:P→P→Prop) (refl : ∀ p, R p p) (trans : ∀ {p q r}, R p q→R q r→R p r)
    (δ:ℝ) (hδ:0<δ) (hE : ∀ p, 0≤E p ∧ E p≤1)
    (hs : ∀ p, ¬Good p → ∃ q, R p q ∧ E p+δ<E q ∧ size q≤size p*4)
    (n:ℕ) (hn : 1<((n:ℝ)+1)*δ) (p:P) :
    ∃ q, Good q ∧ R p q ∧ size q≤size p*4^n := by
  exact energy_termination_aux E size Good R refl trans δ hδ
    (fun p => (hE p).2) hs n p (by linarith [(hE p).1])

#print axioms energy_termination
end SparseHalfGraphon
