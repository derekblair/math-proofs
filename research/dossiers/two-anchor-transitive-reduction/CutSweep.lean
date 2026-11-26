import Mathlib.Tactic

namespace CutSweep
variable {V : Type*}
variable (E : V → V → Prop)

inductive Reach : V → V → Prop
  | nil (u : V) : Reach u u
  | step {u v w : V} : E u v → Reach v w → Reach u w

theorem join {u v w : V} (h : Reach E u v) (y : Reach E v w) : Reach E u w := by
  induction h with
  | nil => exact y
  | step e _ ih => exact .step e (ih y)

variable (rank : V → ℕ) (incr : ∀ u v, E u v → rank u < rank v)

include incr in
theorem rank_mono {u v : V} (h : Reach E u v) : rank u ≤ rank v := by
  induction h with
  | nil => rfl
  | step h _ ih => exact Nat.le_trans (incr _ _ h).le ih

theorem crossing_iff (t : ℕ) (u v : V) (uhl : rank u ≤ t) (vhr : t < rank v) :
    Reach E u v ↔ ∃ x y, Reach E u x ∧ E x y ∧ Reach E y v ∧ rank x ≤ t ∧ t<rank y := by
  constructor
  · intro h
    induction h with
    | nil => omega
    | @step a b c h₀ h₁ ih =>
      by_cases h : rank b ≤ t
      · obtain ⟨x,y,hab,hxy,hyc,hx,hy⟩ := ih h vhr
        exact ⟨x,y,.step h₀ hab,hxy,hyc,hx,hy⟩
      · exact ⟨a,b,.nil _,h₀,h₁,uhl,by omega⟩
  · rintro ⟨x,y,p,h,q,_,_⟩
    exact join E p (.step h q)

def Remove (x y : V) (u v : V) := E u v ∧ ¬(u=x ∧ v=y)

include incr in
theorem prefix_immutable (t : ℕ) (x y : V) (hr : t < rank y) {u v : V}
    (hv : rank v ≤ t) (h : Reach E u v) : Reach (Remove E x y) u v := by
  induction h with
  | nil => exact .nil _
  | @step u b v e p ih =>
    have hh : rank b ≤ rank v := rank_mono E rank incr p
    refine .step ⟨e,?_⟩ (ih hv)
    rintro ⟨_,h⟩
    rw [h] at hh
    omega

include incr in
theorem suffix_immutable (t : ℕ) (x y : V) (hl : rank x ≤ t) {u v : V}
    (hu : t < rank u) (h : Reach E u v) : Reach (Remove E x y) u v := by
  induction h with
  | nil => exact .nil _
  | @step u b v e p ih =>
    have hh : rank u < rank b := incr _ _ e
    refine .step ⟨e,?_⟩ (ih (by omega))
    rintro ⟨h,_⟩
    rw [h] at hu
    omega

theorem remove_subgraph (x y : V) {u v : V} (h : Reach (Remove E x y) u v) :
    Reach E u v := by
  induction h with
  | nil => exact .nil _
  | step e _ ih => exact .step e.1 ih

include incr in
theorem single_rectangle_loss (t : ℕ) (x y s z : V)
    (hl : rank x ≤ t) (hr : t < rank y) (hs : rank s ≤ t) (hz : t < rank z) :
    Reach (Remove E x y) s z ↔
      ∃ u v, Reach E s u ∧ E u v ∧ Reach E v z ∧ rank u ≤ t ∧ t < rank v ∧
        ¬ (u=x ∧ v=y) := by
  rw [crossing_iff (Remove E x y) rank t s z hs hz]
  constructor
  · rintro ⟨u,v,a,b,c,h₁,h₂⟩
    exact ⟨u,v,remove_subgraph E x y a,b.1,remove_subgraph E x y c,h₁,h₂,b.2⟩
  · rintro ⟨u,v,a,b,c,h₁,h₂,hn⟩
    exact ⟨u,v,prefix_immutable E rank incr t x y hr h₁ a,⟨b,hn⟩,
      suffix_immutable E rank incr t x y hl h₂ c,h₁,h₂⟩

theorem counter_loss (s : Finset V) (x : V) [DecidableEq V] (h : x ∈ s) :
    (s.erase x).card + 1 = s.card := Finset.card_erase_add_one h

end CutSweep

#print axioms CutSweep.crossing_iff
#print axioms CutSweep.prefix_immutable
#print axioms CutSweep.suffix_immutable
#print axioms CutSweep.counter_loss

#print axioms CutSweep.single_rectangle_loss
