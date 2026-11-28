import H12DegreeElevenSpecial
import H12DegreeElevenUpper

namespace Erdos151H12
open Erdős151 Erdős151.Upper
open scoped BigOperators
variable {V : Type*} [DecidableEq V] [Fintype V] (G C : V → V → Prop)
variable [DecidableRel G] [DecidableRel C]

/-- The ambient degree-eleven rows sufficient for the unified argument.
Only total slot counting is required; no enumeration of peripheral owner pairs. -/
theorem degreeEleven_at_least53
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (tf : TriangleFreeLinks G)
    (sub : ∀ {a b}, C a b → G a b) (two : TwoTriangles C)
    (degree : ∀ v, (neighbors G v).card ≤ 11)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card ≤ 11)
    (hn : 53 ≤ Fintype.card V)
    (w : V) (h11 : (neighbors G w).card = 11)
    (cmin : ∀ u∈neighbors C w, 8 ≤ (neighbors C u).card)
    (e : Nat) (he : ∑ u∈neighbors C w,row C (neighbors C w) u = 2*e) :
    ((neighbors C w).card = 9 → e ≤ 13) ∧
    ((neighbors C w).card = 10 → e ≤ 11) ∧
    ((neighbors C w).card = 11 → e ≤ 10) := by
  classical
  let S := neighbors G w
  let X := ext S w
  let A := (specialCols G S X).card
  let I := ∑ x∈X,ncol G S x
  let ell := ∑ x∈X,lcol G S x
  have hS : Free (Forbidden G) (S : Set V) := by
    have h := neighborhood_free G sym tf w
    convert h using 1
    ext x
    exact mem_neighbors G
  have hXS : Disjoint X S := Finset.disjoint_left.mpr (by
    intro x hx hxS
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hxS))
  have hS11 : S.card = 11 := h11
  have hx41 : 41 ≤ X.card := by
    have hwS : w ∉ S := fun hw => irr w ((mem_neighbors G).mp hw)
    change 41 ≤ ((Finset.univ : Finset V) \ insert w S).card
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_insert_of_notMem hwS,hS11]
    omega
  have hLo := degreeEleven_lower_incidence G S X sym irr tf hS11 hS hXS upper
  have hSpec := degreeEleven_special_cost G S X sym irr tf hS11 hS hXS upper
  obtain ⟨hI,hL⟩ := degreeEleven_upper_slots G C sym irr sub two degree w h11 cmin e he
  change 3*X.card ≤ I+11+A at hLo
  change 2*A ≤ ell+11 at hSpec
  change I+2*e ≤ 110 at hI
  change ell+7*(neighbors C w).card ≤110 at hL
  omega

#print axioms degreeEleven_at_least53
end Erdos151H12
