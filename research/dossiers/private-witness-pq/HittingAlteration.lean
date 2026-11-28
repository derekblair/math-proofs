import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

namespace CatalogAlteration
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Every trial set must miss enough supports. Repair it by adding
one vertex from each support it missed; the size of the repaired
hitting set gives a pointwise lower bound. -/
theorem missed_at_least (F : Finset (Finset V)) (c : ℕ)
    (nonempty : ∀ E ∈ F, E.Nonempty)
    (no : ∀ T : Finset V, T.card ≤ c → ∃ E ∈ F, Disjoint T E)
    (S : Finset V) :
    c+1 ≤ S.card + (F.filter (Disjoint S)).card := by
  classical
  let M := F.filter (Disjoint S)
  let pick (E : ↥M) : V := (nonempty E.val ((Finset.mem_filter.mp E.property).1)).choose
  have mem_pick (E : ↥M) : pick E ∈ E.val :=
    (nonempty E.val ((Finset.mem_filter.mp E.property).1)).choose_spec
  let P := (Finset.univ : Finset ↥M).image pick
  have cap : P.card ≤ M.card := by
    have h := (Finset.card_image_le (s := (Finset.univ : Finset ↥M)) (f := pick))
    simpa only [P,Finset.card_univ,Fintype.card_coe] using h
  have hcard := Finset.card_union_le (s := S) (t := P)
  by_contra hn
  change ¬ c+1 ≤ S.card + M.card at hn
  obtain ⟨E,hEF,dis⟩ := no (S∪P) (by omega)
  have es : Disjoint S E := dis.mono_left (Finset.subset_union_left)
  have em : E∈M := Finset.mem_filter.mpr ⟨hEF,es⟩
  let e : ↥M := ⟨E,em⟩
  have hp : pick e ∈ P := Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
  exact Finset.disjoint_left.mp dis (Finset.mem_union_right _ hp) (mem_pick e)

#print axioms missed_at_least
end CatalogAlteration
