import BoxRoster
import Mathlib.Data.Finset.Card

namespace DirectedBoxDSP
open BoxRoster

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

universe u

inductive SplitTree (V : Type u) [DecidableEq V] : Finset V → Type u where
  | leaf (S : Finset V) : SplitTree V S
  | node {L R : Finset V} : Disjoint L R → SplitTree V L → SplitTree V R →
      SplitTree V (L ∪ R)

variable (tail head : A → V) (accept : V → Finset A → Prop) (cap : ℕ)

def treeAccept : {S : Finset V} → SplitTree V S → Finset A → Prop
  | S, .leaf _, B => B.card ≤ cap ∧ ∃ F, realizes tail head S B accept F
  | _, .node (L := L) (R := R) _ l r, B => B.card ≤ cap ∧ ∃ BL BR,
      treeAccept l BL ∧ treeAccept r BR ∧
      touch tail head R BL = touch tail head L BR ∧
      B = away tail head R BL ∪ away tail head L BR

/-- Soundness of the bounded-roster recursion: the two child witnesses
can always be joined without modifying any local incidence constraint. -/
theorem tree_sound {S : Finset V} (tree : SplitTree V S) :
    ∀ B, treeAccept tail head accept cap tree B → ∃ F, realizes tail head S B accept F := by
  induction tree with
  | leaf U =>
    intro B h
    exact h.2
  | @node L R hd l r hl hr =>
    intro B h
    obtain ⟨_,BL,BR,hL,hR,hm,he⟩ := h
    obtain ⟨FL,hFL⟩ := hl BL hL
    obtain ⟨FR,hFR⟩ := hr BR hR
    exact (split_iff tail head L R B accept hd).mpr ⟨BL,BR,FL,FR,hFL,hFR,hm,he⟩


def treeBounded : {S : Finset V} → SplitTree V S → Finset A → Prop
  | S, .leaf _, F => (boundary tail head S F).card ≤ cap
  | _, .node (L := L) (R := R) _ l r, F => (boundary tail head (L ∪ R) F).card ≤ cap ∧
      treeBounded l F ∧ treeBounded r F

theorem boundary_restrict (S : Finset V) (F : Finset A) :
    boundary tail head S (touch tail head S F) = boundary tail head S F := by
  ext a
  simp only [mem_boundary, mem_touch]
  tauto

theorem restricted_realizes (S : Finset V) (F : Finset A)
    (h : ∀ x ∈ S, accept x (roster tail head x F)) :
    realizes tail head S (boundary tail head S F) accept (touch tail head S F) := by
  refine ⟨(confined_iff tail head S _).mpr ?_, boundary_restrict tail head S F, ?_⟩
  · intro a ha
    exact (mem_touch _ _ _ _ _).mp ha |>.2
  · intro x hx
    rw [roster_restrict tail head hx]
    exact h x hx

/-- Completeness for a solution with some bounded tree of subdivisions. Unlike
soundness, completeness does not assert that every tree admits this solution. -/
theorem tree_complete {S : Finset V} (tree : SplitTree V S) (F : Finset A) :
    treeBounded tail head cap tree F → (∀ x ∈ S, accept x (roster tail head x F)) →
    treeAccept tail head accept cap tree (boundary tail head S F) := by
  induction tree with
  | leaf U =>
    intro hcap h
    exact ⟨hcap, touch tail head U F, restricted_realizes tail head accept U F h⟩
  | @node L R hd l r hl hr =>
    intro hb h
    obtain ⟨hcap, hbL, hbR⟩ := hb
    have accL : ∀ x ∈ L, accept x (roster tail head x F) :=
      fun x hx => h x (Finset.mem_union_left _ hx)
    have accR : ∀ x ∈ R, accept x (roster tail head x F) :=
      fun x hx => h x (Finset.mem_union_right _ hx)
    have realL := restricted_realizes tail head accept L F accL
    have realR := restricted_realizes tail head accept R F accR
    have hag : agree tail head L R (touch tail head L F) (touch tail head R F) := by
      constructor <;> intro a ha <;> simp only [mem_touch] at ha ⊢ <;> tauto
    refine ⟨hcap, boundary tail head L F, boundary tail head R F,
      hl hbL accL, hr hbR accR, ?_, ?_⟩
    · have h' := (agree_from_boundary tail head L R _ _ hd realL.1 realR.1).mp hag
      simpa only [boundary_restrict] using h'
    · simpa only [boundary_restrict] using boundary_decomp tail head L R F hd

#print axioms tree_sound
#print axioms tree_complete
end DirectedBoxDSP
