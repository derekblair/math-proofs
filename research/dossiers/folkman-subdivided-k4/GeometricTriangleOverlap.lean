import GeometricVariance
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

namespace RobustFolkman.Moment
open Finset
variable {V : Type*} [DecidableEq V]

theorem triangle_overlap_row (U i : Finset V) (hi : i ∈ U.powersetCard 3) :
    (((U.powersetCard 3).erase i).filter (fun j => (j ∩ i).card = 2)).card ≤
      3*(U.card-3) := by
  let E := ((U.powersetCard 3).erase i).filter (fun j => (j ∩ i).card = 2)
  let D := (i.powersetCard 2) ×ˢ ((U \ i).powersetCard 1)
  have h : E.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun j => (j∩i,j\i))
    · intro j hj
      obtain ⟨hj, inter⟩ := mem_filter.mp (show j∈E from hj)
      obtain ⟨sub, hj3⟩ := mem_powersetCard.mp (mem_of_mem_erase hj)
      change (j∩i,j\i)∈D
      rw [show (j∩i,j\i)∈D ↔ _ from Finset.mem_product, mem_powersetCard, mem_powersetCard]
      refine ⟨⟨inter_subset_right,inter⟩,⟨?_,?_⟩⟩
      · intro x hx
        exact mem_sdiff.mpr ⟨sub (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff,hj3,inter_comm i j,inter]
    · intro j _ k _ eq
      have a := congrArg Prod.fst eq
      have b := congrArg Prod.snd eq
      have split (s : Finset V) : (s\i) ∪ (s∩i) = s := by ext x; simp; tauto
      calc
        j = (j\i) ∪ (j∩i) := (split j).symm
        _ = (k\i) ∪ (k∩i) := congrArg₂ (fun (x y : Finset V) => x∪y) b a
        _ = k := split k
  have hd : D.card=3*(U.card-3) := by
    rw [show D.card = (i.powersetCard 2).card * ((U\i).powersetCard 1).card from
      Finset.card_product _ _,Finset.card_powersetCard,Finset.card_powersetCard,
      (mem_powersetCard.mp hi).2, Nat.choose_one_right,
      Finset.card_sdiff_of_subset (mem_powersetCard.mp hi).1,(mem_powersetCard.mp hi).2]
    rfl
  exact h.trans_eq hd

variable {Ω 𝕜 : Type*} [Fintype Ω] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The exact combinatorial coefficients for the spherical triangle variance
step. The distribution need only supply the individual and pair moments. -/
theorem triangle_variance_upper (p : Ω → 𝕜) (p1 : (∑ ω, p ω)=1)
    (U : Finset V) (f : Finset V → Ω → 𝕜) (μ q : 𝕜) (q0 : 0≤q)
    (sq : ∀ i ω, f i ω*f i ω=f i ω)
    (m : ∀ i ∈ U.powersetCard 3, mean p (f i)=μ)
    (no : ∀ i j, i ∈ U.powersetCard 3 → j ∈ U.powersetCard 3 → i ≠ j →
      (j ∩ i).card ≠ 2 → mean p (fun ω => f i ω*f j ω) ≤ μ^2)
    (yes : ∀ i j, i ∈ U.powersetCard 3 → j ∈ U.powersetCard 3 → i ≠ j →
      (j ∩ i).card = 2 → mean p (fun ω => f i ω*f j ω) ≤ q) :
    mean p (fun ω => ((∑ i ∈ U.powersetCard 3, f i ω)-(↑(U.card.choose 3) : 𝕜)*μ)^2) ≤
      (↑(U.card.choose 3) : 𝕜)*(μ+(↑(3*(U.card-3)) : 𝕜)*q) := by
  classical
  rw [←Finset.card_powersetCard]
  apply (variance_indicator_upper p p1 (U.powersetCard 3) f μ q sq m
    (fun i j => (j∩i).card=2) no yes).trans
  have rows : (∑ i ∈ U.powersetCard 3, (↑((((U.powersetCard 3).erase i).filter
      (fun j => (j∩i).card=2)).card) : 𝕜)*q) ≤
        (↑((U.powersetCard 3).card) : 𝕜)*((↑(3*(U.card-3)) : 𝕜)*q) := by
    calc
      _ ≤ ∑ _i ∈ U.powersetCard 3, (↑(3*(U.card-3)) : 𝕜)*q := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast triangle_overlap_row U i hi) q0
      _ = _ := by simp
  rw [mul_add]
  exact add_le_add_right rows _

#print axioms triangle_variance_upper
end RobustFolkman.Moment
