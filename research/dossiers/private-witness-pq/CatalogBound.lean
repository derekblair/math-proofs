import HittingAlteration
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
namespace CatalogAlteration

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite, division-free form of the repair lower bound. It is exact
for every trial size s, and being purely combinatorial assumes nothing
about the computational hardness of a cryptosystem. -/
theorem altered_cover_lower (F : Finset (Finset V)) (c r s : ℕ)
    (rp : 0 < r) (uniform : ∀ E ∈ F, E.card=r)
    (no : ∀ T : Finset V, T.card ≤ c → ∃ E ∈ F, Disjoint T E) :
    (c+1-s) * (Fintype.card V).choose s ≤ F.card * (Fintype.card V-r).choose s := by
  classical
  let P := (Finset.univ : Finset V).powersetCard s
  have ne : ∀ E ∈ F, E.Nonempty := fun E h =>
    Finset.card_pos.mp (by rw [uniform E h];exact rp)
  have pcard : P.card = (Fintype.card V).choose s := by
    simp [P,Finset.card_powersetCard]
  have lb (S : Finset V) (h : S∈P) : c+1-s ≤ (F.filter (Disjoint S)).card := by
    have sc := (Finset.mem_powersetCard.mp h).2
    have lhs := missed_at_least F c ne no S
    omega
  have row (S : Finset V) :
      (F.filter (Disjoint S)).card = ∑ E∈F, if Disjoint S E then 1 else 0 := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have inner (E : Finset V) (he : E∈F) :
      (P.filter (fun S => Disjoint S E)).card = (Fintype.card V-r).choose s := by
    have eq : P.filter (fun S => Disjoint S E) = ((Finset.univ : Finset V)\E).powersetCard s := by
      ext S
      simp only [Finset.mem_filter,Finset.mem_powersetCard,P]
      constructor
      · rintro ⟨⟨_,hcard⟩,hdis⟩
        exact ⟨fun v hv => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hdis hv⟩,
          hcard⟩
      · rintro ⟨hh,hcard⟩
        exact ⟨⟨Finset.subset_univ _,hcard⟩,
          Finset.disjoint_left.mpr (fun v hv => (Finset.mem_sdiff.mp (hh hv)).2)⟩
    rw [eq,Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ E),
      Finset.card_univ,uniform E he]
  calc
    (c+1-s) * (Fintype.card V).choose s = ∑ _S∈P, (c+1-s) := by
      rw [Finset.sum_const,pcard,Nat.mul_comm]
      rfl
    _ ≤ ∑ S∈P, (F.filter (Disjoint S)).card := Finset.sum_le_sum lb
    _ = ∑ E∈F, (P.filter (fun S => Disjoint S E)).card := by
      simp_rw [row]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_filter,← Finset.card_eq_sum_ones]
    _ = F.card * (Fintype.card V-r).choose s := by
      rw [Finset.sum_congr rfl inner,Finset.sum_const]
      rfl

#print axioms altered_cover_lower
end CatalogAlteration
