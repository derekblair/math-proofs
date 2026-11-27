import TightCubicContraction
import TightSquare

namespace FolkmanB4.Tight
open Finset Critical
variable {L V : Type*} [Fintype L] [Fintype V] [DecidableEq L] [DecidableEq V]

structure Square (I : L → V → Prop) where
  l₁ : L
  l₂ : L
  v₁ : V
  v₂ : V
  lne : l₁ ≠ l₂
  vne : v₁ ≠ v₂
  e₁₁ : I l₁ v₁
  e₁₂ : I l₁ v₂
  e₂₁ : I l₂ v₁
  e₂₂ : I l₂ v₂

def Square.edges {I : L → V → Prop} (s : Square I) : Finset (L × V) :=
  {(s.l₁,s.v₁),(s.l₁,s.v₂),(s.l₂,s.v₁),(s.l₂,s.v₂)}

theorem Square.central {I : L → V → Prop} [DecidableRel I] (s : Square I)
    (H : NoSmallCut I) (M : ∃ m : V ≃ L, ∀ v, I (m v) v) :
    ∃ m : V ≃ L, (∀ v, I (m v) v) ∧ I (m s.v₂) s.v₁ ∧ I (m s.v₁) s.v₂ := by
  obtain ⟨m,x,y,M'⟩ := robust_two_extend I H M s.lne s.vne s.e₁₁ s.e₂₂
  exact ⟨m,M',by rw [y]; exact s.e₂₁,by rw [x]; exact s.e₁₂⟩

/-- Two edge-disjoint squares cannot both touch a fixed vertex of degree
at most three. This is precisely the exclusion needed at a contracted port. -/
theorem Square.off_column_of_disjoint {I : L → V → Prop} [DecidableRel I]
    (s t : Square I) (sep : Disjoint s.edges t.edges) (u : V) (deg : lns I u ≤ 3) :
    (s.v₁≠u ∧ s.v₂≠u) ∨ (t.v₁≠u ∧ t.v₂≠u) := by
  classical
  by_contra no
  push Not at no
  obtain ⟨su0,tu0⟩ := no
  have su : s.v₁=u ∨ s.v₂=u := by by_cases h : s.v₁=u; exact Or.inl h; exact Or.inr (su0 h)
  have tu : t.v₁=u ∨ t.v₂=u := by by_cases h : t.v₁=u; exact Or.inl h; exact Or.inr (tu0 h)
  have cs : I s.l₁ u ∧ I s.l₂ u := by
    rcases su with h|h
    · exact h ▸ ⟨s.e₁₁,s.e₂₁⟩
    · exact h ▸ ⟨s.e₁₂,s.e₂₂⟩
  have ct : I t.l₁ u ∧ I t.l₂ u := by
    rcases tu with h|h
    · exact h ▸ ⟨t.e₁₁,t.e₂₁⟩
    · exact h ▸ ⟨t.e₁₂,t.e₂₂⟩
  have rowsdis (a : L) (sa : a=s.l₁ ∨ a=s.l₂) (ta : a=t.l₁ ∨ a=t.l₂) : False := by
    have sep' : ∀ ⦃z : L × V⦄, z∈s.edges → z∉t.edges := disjoint_left.mp sep
    apply @sep' (a,u)
    · rcases sa with e|e <;> rcases su with w|w <;> simp [Square.edges,e,←w]
    · rcases ta with e|e <;> rcases tu with w|w <;> simp [Square.edges,e,←w]
  have h₁₁ : s.l₁ ≠ t.l₁ := fun h => rowsdis _ (Or.inl rfl) (Or.inl h)
  have h₁₂ : s.l₁ ≠ t.l₂ := fun h => rowsdis _ (Or.inl rfl) (Or.inr h)
  have h₂₁ : s.l₂ ≠ t.l₁ := fun h => rowsdis _ (Or.inr rfl) (Or.inl h)
  have h₂₂ : s.l₂ ≠ t.l₂ := fun h => rowsdis _ (Or.inr rfl) (Or.inr h)
  let R : Finset L := {s.l₁,s.l₂,t.l₁,t.l₂}
  have size : R.card=4 := by simp [R,s.lne,t.lne,h₁₁,h₁₂,h₂₁,h₂₂]
  have sub : R⊆univ.filter (fun l => I l u) := by
    intro l hl
    simp [R] at hl
    rcases hl with rfl|rfl|rfl|rfl
    · simp [cs.1]
    · simp [cs.2]
    · simp [ct.1]
    · simp [ct.2]
  have bound := card_le_card sub
  change R.card ≤ lns I u at bound
  omega

#print axioms Square.central
#print axioms Square.off_column_of_disjoint
end FolkmanB4.Tight
