import CriticalTransport

namespace FolkmanB4.Critical

/-- With the all-positive matching sign condition, two cross edges of a
central square cannot coexist. Swapping their two matched columns would
reverse the sign, while retaining a supported perfect matching. -/
theorem no_switch_square {L V : Type*} [Fintype V] [DecidableEq V]
    (I : L → V → Prop) (e : V ≃ L)
    (signs : ∀ s t : V ≃ L, (∀ i, I (s i) i) → (∀ i, I (t i) i) →
        pSign (s.trans e.symm) = pSign (t.trans e.symm))
    (s : V ≃ L) (hs : ∀ i, I (s i) i)
    {a b : V} (distinct : a≠b) (ha : I (s b) a) (hb : I (s a) b) : False := by
  classical
  let swap := Equiv.swap a b
  let t := swap.trans s
  have ht (i : V) : I (t i) i := by
    by_cases ia : i=a
    · subst i
      simpa [t,swap] using ha
    by_cases ib : i=b
    · subst i
      simpa [t,swap] using hb
    · have hswap : swap i=i := Equiv.swap_apply_of_ne_of_ne ia ib
      simpa [t,hswap] using hs i
  have h := signs s t hs ht
  have opposite : pSign (t.trans e.symm) = -pSign (s.trans e.symm) := by
    change pSign ((Equiv.swap a b).trans (s.trans e.symm)) = _
    unfold pSign
    rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap distinct]
    simp
  rw [opposite] at h
  rcases pSign_vals (s.trans e.symm) with h' | h' <;> rw [h'] at h <;> norm_num at h

#print axioms no_switch_square
end FolkmanB4.Critical
