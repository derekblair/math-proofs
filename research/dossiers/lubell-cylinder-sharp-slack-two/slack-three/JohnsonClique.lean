import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace LubellSlackThree
open Finset

private theorem card_inter_strict {α : Type*} [DecidableEq α]
    (g x : Finset α) (h : ¬x⊆g) : (g∩x).card<x.card := by
  have sub : g∩x⊆x := inter_subset_right
  apply Nat.lt_of_le_of_ne (card_le_card sub)
  intro eq
  have E : g∩x=x := eq_of_subset_of_card_le sub (by omega)
  apply h
  intro i hi
  have H : i∈g∩x := by rwa [E]
  exact (mem_inter.mp H).1

/-- A clique in a Johnson graph is a star or lies in one top. -/
theorem johnson_star_or_top {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (k : Nat) (hk : 1≤k) (two : 1<F.card)
    (size : ∀ a∈F, a.card=k)
    (near : ∀ a∈F, ∀ b∈F, k-1≤(a∩b).card) :
    (∃ x : Finset α, x.card=k-1 ∧ ∀ g∈F, x⊆g) ∨
    (∃ v : Finset α, v.card=k+1 ∧ ∀ g∈F, g⊆v) := by
  classical
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp two
  let X := a∩b
  let V := a∪b
  have sa := size a ha
  have sb := size b hb
  have subnot : ¬b⊆a := by
    intro sub
    have eq := eq_of_subset_of_card_le sub (by omega)
    exact hab eq.symm
  have hX : X.card=k-1 := by
    have l := near a ha b hb
    have u := card_inter_strict a b subnot
    dsimp [X]
    omega
  have hV : V.card=k+1 := by
    have C := card_union_add_card_inter a b
    change V.card+X.card=a.card+b.card at C
    omega
  by_cases all : ∀ g∈F, X⊆g
  · exact Or.inl ⟨X,hX,all⟩
  · have notStarInTop (g : Finset α) (hg : g∈F) (h : ¬X⊆g) : g⊆V := by
      have C := card_union_add_card_inter (g∩a) (g∩b)
      have E1 : (g∩a)∪(g∩b)=g∩V := by
        ext z
        simp [V, and_or_left]
      have E2 : (g∩a)∩(g∩b)=g∩X := by
        ext z
        simp [X, and_assoc, and_left_comm]
      rw [E1,E2] at C
      have h1 := near g hg a ha
      have h2 := near g hg b hb
      have hI := card_inter_strict g X h
      have hgsize := size g hg
      have sub : g∩V⊆g := inter_subset_left
      have E := eq_of_subset_of_card_le sub (by omega : g.card≤(g∩V).card)
      intro z hz
      have G : z∈g∩V := by rwa [E]
      exact (mem_inter.mp G).2
    have existsH : ∃ h∈F, ¬X⊆h := by
      by_contra no
      exact all (fun h hh => by by_contra n; exact no ⟨h,hh,n⟩)
    obtain ⟨h,hh,hn⟩ := existsH
    have hSub := notStarInTop h hh hn
    refine Or.inr ⟨V,hV,?_⟩
    intro g hg
    by_cases sg : X⊆g
    · by_contra notTop
      have hsmall : (g∩V).card<g.card := by
        simpa only [inter_comm] using card_inter_strict V g notTop
      have sub : X⊆g∩V := by
        intro i hi
        refine mem_inter.mpr ⟨sg hi,?_⟩
        exact mem_union.mpr (Or.inl (mem_inter.mp hi).1)
      have hs := size g hg
      have E : X=g∩V := eq_of_subset_of_card_le sub (by omega)
      have H : g∩h⊆h∩X := by
        intro z hz
        obtain ⟨hz1,hz2⟩ := mem_inter.mp hz
        exact mem_inter.mpr ⟨hz2,by rw [E]; exact mem_inter.mpr ⟨hz1,hSub hz2⟩⟩
      have hl := card_le_card H
      have hr := card_inter_strict h X hn
      have l := near g hg h hh
      omega
    · exact notStarInTop g hg sg

end LubellSlackThree
#print axioms LubellSlackThree.johnson_star_or_top
