import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

namespace CatalogAlteration
open scoped BigOperators

variable {V T : Type*} [Fintype V] [DecidableEq V]

/-- The exact witness acceptance multiplicity for a single padded
transcript. No assumptions on how the transcript chose its sites. -/
theorem disjoint_witness_count (D : Finset V) (f : ℕ) :
    (((Finset.univ : Finset V).powersetCard f).filter (fun S => Disjoint S D)).card =
      (Fintype.card V - D.card).choose f := by
  have eq : ((Finset.univ : Finset V).powersetCard f).filter (fun S => Disjoint S D) =
      ((Finset.univ : Finset V) \ D).powersetCard f := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_,hcard⟩,hdis⟩
      exact ⟨fun v hv => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hdis hv⟩,
        hcard⟩
    · rintro ⟨hh,hcard⟩
      exact ⟨⟨Finset.subset_univ _,hcard⟩,
        Finset.disjoint_left.mpr (fun v hv => (Finset.mem_sdiff.mp (hh hv)).2)⟩
  rw [eq,Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ D),
    Finset.card_univ]

/-- If the real transcript law is independent of a hidden uniform witness,
summing the accepted transcript weights over disjoint witnesses multiplies
them by the same constant. This identity does not prove that independence
for any particular cryptographic simulation. -/
theorem padded_weight_factor {K : Type*} [CommSemiring K]
    (accept : Finset T) (pad : T → Finset V) (mass : T → K) (c f : ℕ)
    (padsize : ∀ t ∈ accept, (pad t).card=c) :
    (∑ t ∈ accept, mass t *
      (↑((((Finset.univ : Finset V).powersetCard f).filter
        (fun S => Disjoint S (pad t))).card) : K)) =
      ((Fintype.card V-c).choose f : K) * ∑ t ∈ accept, mass t := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [disjoint_witness_count, padsize t ht, mul_comm]

#print axioms disjoint_witness_count
#print axioms padded_weight_factor
end CatalogAlteration
