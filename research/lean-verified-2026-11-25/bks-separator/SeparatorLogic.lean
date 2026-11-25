import Mathlib.Order.Basic
import Mathlib.Logic.Relation

namespace PackingSeparator

def Inc {α : Type} [PartialOrder α] (x y : α) : Prop := ¬x≤y ∧ ¬y≤x

def Separator {α : Type} [PartialOrder α] (z : α) : Prop :=
  (∀ x, x≤z ∨ z≤x) ∧
  (∃ x y, x<z ∧ y<z ∧ Inc x y) ∧
  (∃ x y, z<x ∧ z<y ∧ Inc x y)

lemma inc_stays_below {α : Type} [PartialOrder α] {z x y : α}
    (hc : ∀ w, w≤z ∨ z≤w) (hx : x<z) (he : Inc x y) : y<z := by
  have H := hc y
  rcases H with le|ge
  · have ne : y≠z := by intro E; subst y; exact he.1 hx.le
    exact lt_of_le_of_ne le ne
  · exact (he.1 (hx.le.trans ge)).elim

lemma inc_symm {α : Type} [PartialOrder α] {x y : α} (E : Inc x y) : Inc y x := E.symm

lemma walk_stays_below {α : Type} [PartialOrder α] {z x y : α}
    (hc : ∀ w, w≤z ∨ z≤w)
    (path : Relation.ReflTransGen Inc x y) (hx : x<z) : y<z := by
  induction path with
  | refl => exact hx
  | @tail a b p e ih => exact inc_stays_below hc ih e

lemma single_nontrivial_component_blocks {α : Type} [PartialOrder α]
    (h : ∀ a b c d : α, Inc a b → Inc c d → Relation.ReflTransGen Inc a c) :
    ∀ z : α, ¬ Separator z := by
  intro z S
  obtain ⟨comp,⟨a,b,ha,hb,hab⟩,⟨c,d,hc,hd,hcd⟩⟩ := S
  have C := walk_stays_below comp (h a b c d hab hcd) ha
  exact (not_lt_of_ge hc.le) C

/-- A sufficient connected middle test: every incomparable pair has at
least one endpoint joined to the fixed middle, and each point of the middle
is joined to the fixed representative. -/
lemma connected_middle_blocks {α : Type} [PartialOrder α] {mid : α → Prop} (v : α)
    (conn : ∀ x, mid x → Relation.ReflTransGen Inc x v)
    (edges : ∀ x y : α, Inc x y → mid x ∨ mid y) : ∀ z : α, ¬ Separator z := by
  have hit (a b : α) (e : Inc a b) : Relation.ReflTransGen Inc a v := by
    rcases edges a b e with ha|hb
    · exact conn a ha
    · exact (Relation.ReflTransGen.single e).trans (conn b hb)
  have symm {x y : α} (h : Relation.ReflTransGen Inc x y) : Relation.ReflTransGen Inc y x := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b p e ih =>
      exact (Relation.ReflTransGen.single (inc_symm e)).trans ih
  apply single_nontrivial_component_blocks
  intro a b c d ha hb
  exact (hit a b ha).trans (symm (hit c d hb))

end PackingSeparator
