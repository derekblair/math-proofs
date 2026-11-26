import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace AdditiveLabelCriterion

universe u
variable {A B C : Type u}

abbrev Base (A B C : Type u) := (A ⊕ B ⊕ C) →₀ ℤ

noncomputable def atom (v : A ⊕ B ⊕ C) : Base A B C := Finsupp.single v 1

noncomputable def row (a : A) (b : B) (c : C) : Base A B C :=
  atom (Sum.inl a) + atom (Sum.inr (Sum.inl b)) + atom (Sum.inr (Sum.inr c))

noncomputable def forced (E : A → B → C → Prop) : AddSubgroup (Base A B C) :=
  AddSubgroup.closure {x | ∃ a b c, E a b c ∧ x = row a b c}

theorem necessary {G : Type*} [AddCommGroup G] (E : A→B→C→Prop)
    (f : A→G) (g : B→G) (h : C→G)
    (exact_code : ∀ a b c, E a b c ↔ f a+g b+h c=0) (a : A) (b : B) (c : C)
    (hr : row a b c ∈ forced E) : E a b c := by
  let labels := Sum.elim f (Sum.elim g h)
  let l (v : A ⊕ B ⊕ C) : ℤ →+ G :=
    ⟨⟨fun n => n • labels v,by simp⟩, fun _ _ => add_zsmul _ _ _⟩
  let eval := Finsupp.liftAddHom l
  have ev (a : A) (b : B) (c : C) : eval (row a b c) = f a+g b+h c := by
    unfold row
    rw [map_add,map_add]
    simp only [eval,atom,Finsupp.liftAddHom_apply_single]
    simp [l,labels]
  have sub : forced E ≤ eval.ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro x hx
    obtain ⟨a,b,c,he,rfl⟩ := hx
    exact (ev a b c).trans ((exact_code a b c).mp he)
  exact (exact_code a b c).mpr ((ev _ _ _).symm.trans (sub hr))

/-- A set of triples admits an exact additive encoding iff no forbidden
triple lies in the integer subgroup spanned by the required triples.
The universal encoding is the quotient by that subgroup. -/
theorem quotient_labels (E : A→B→C→Prop)
    (closed : ∀ a b c, row a b c ∈ forced E → E a b c) :
    ∃ (f : A → (Base A B C ⧸ forced E)) (g : B → (Base A B C ⧸ forced E))
      (h : C → (Base A B C ⧸ forced E)), ∀ a b c, E a b c ↔ f a + g b + h c = 0 := by
  let q := QuotientAddGroup.mk' (forced E)
  refine ⟨fun a => q (atom (Sum.inl a)),fun b => q (atom (Sum.inr (Sum.inl b))),
    fun c => q (atom (Sum.inr (Sum.inr c))),?_⟩
  intro a b c
  rw [← map_add,← map_add]
  change E a b c ↔ (↑(row a b c) : Base A B C ⧸ forced E) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨fun he => AddSubgroup.subset_closure ⟨a,b,c,he,rfl⟩,closed a b c⟩

end AdditiveLabelCriterion
#print axioms AdditiveLabelCriterion.necessary
#print axioms AdditiveLabelCriterion.quotient_labels
