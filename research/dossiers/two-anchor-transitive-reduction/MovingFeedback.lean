import Mathlib.Tactic

namespace MovingFeedback
variable {V : Type*}

def Complement (G : V → V → Prop) (F : V → Prop) (u v : V) :=
  G u v ∧ ¬F u ∧ ¬F v

def Drop (G₀ G₁ : V → V → Prop) (F₀ F₁ : V → Prop) (u v : V) :=
  (G₀ u v ∧ ¬G₁ u v ∧ ¬F₀ u ∧ ¬F₀ v) ∨
    (Complement G₀ F₀ u v ∧ G₁ u v ∧ ((F₁ u ∧ ¬F₀ u) ∨ (F₁ v ∧ ¬F₀ v)))

theorem drop_exact (G₀ G₁ : V → V → Prop) (F₀ F₁ : V → Prop) (u v : V) :
    Drop G₀ G₁ F₀ F₁ u v ↔ Complement G₀ F₀ u v ∧ ¬Complement G₁ F₁ u v := by
  classical
  unfold Drop Complement
  tauto

theorem admitted_arc_origin (G₀ G₁ : V → V → Prop) (F₀ F₁ : V → Prop)
    (u v : V) (new : Complement G₁ F₁ u v) (old : ¬Complement G₀ F₀ u v) :
    (G₁ u v ∧ ¬G₀ u v) ∨ (F₀ u ∧ ¬F₁ u) ∨ (F₀ v ∧ ¬F₁ v) := by
  classical
  unfold Complement at *
  tauto

theorem safe_subset_order (G H : V → V → Prop) (rank : V → ℕ)
    (safe : ∀ u v, H u v → rank u < rank v) (sub : ∀ u v, G u v → H u v) :
    ∀ u v, G u v → rank u < rank v := by
  intro u v h
  exact safe u v (sub u v h)

end MovingFeedback

#print axioms MovingFeedback.drop_exact
#print axioms MovingFeedback.admitted_arc_origin
#print axioms MovingFeedback.safe_subset_order
