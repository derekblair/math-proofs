import Mathlib.Tactic

namespace TwoAnchor

variable {V : Type*} (E : V → V → Prop) (F : V → Prop)

inductive Reach : V → V → Prop
  | nil (x : V) : Reach x x
  | step {u v w : V} : E u v → Reach v w → Reach u w

theorem join {x y z : V} (p : Reach E x y) (q : Reach E y z) : Reach E x z := by
  induction p with
  | nil => exact q
  | step e w ih => exact .step e (ih q)

theorem hits_anchor (rank : V → ℕ)
    (decreases : ∀ u v, ¬F u → ¬F v → E u v → rank v < rank u)
    (positive : ∀ u, ∃ v, E u v) (u : V) :
    ∃ w, F w ∧ Reach E u w := by
  classical
  induction h : rank u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hu : F u
    · exact ⟨u,hu,.nil u⟩
    · obtain ⟨v,e⟩ := positive u
      by_cases hv : F v
      · exact ⟨v,hv,.step e (.nil v)⟩
      · have hvlt := decreases u v hu hv e
        rw [h] at hvlt
        obtain ⟨w,hw,p⟩ := ih (rank v) hvlt v rfl
        exact ⟨w,hw,.step e p⟩

theorem reverse {x y : V} (p : Reach (fun u v => E v u) x y) : Reach E y x := by
  induction p with
  | nil => exact .nil _
  | step e _ ih => exact join E ih (.step e (.nil _))

theorem degree_anchor_connected (rank : V → ℕ) (N : ℕ)
    (upper : ∀ v, rank v ≤ N)
    (decreases : ∀ u v, ¬F u → ¬F v → E u v → rank v < rank u)
    (positive : ∀ u, ∃ v, E u v) (negative : ∀ v, ∃ u, E u v)
    (anchored : ∀ x y, F x → F y → Reach E x y)
    (x y : V) : Reach E x y := by
  obtain ⟨a,ha,p⟩ := hits_anchor E F rank decreases positive x
  have rev_dec : ∀ u v, ¬ F u → ¬ F v → E v u → N-rank v < N-rank u := by
    intro u v hu hv e
    have el := decreases v u hv hu e
    have b := upper v
    omega
  obtain ⟨b,hb,q⟩ := hits_anchor (fun u v => E v u) F (fun v => N-rank v) rev_dec negative y
  exact join E (join E p (anchored a b ha hb)) (reverse E q)

theorem permanent_block (before after : ℕ) (hb : before=1)
    (mono : after≤before) (positive : 1≤after) : after=1 := by omega

theorem optional_essential (n m : ℕ) (minimal : n≤m) (smaller : m+1≤n) : False := by omega

end TwoAnchor

#print axioms TwoAnchor.degree_anchor_connected
#print axioms TwoAnchor.permanent_block
#print axioms TwoAnchor.optional_essential
