import HubTripleSafe
import ThreeHubCount
import LargePoolTen

namespace Erdos151H13
open Erdős151 Erdos151H12

variable {V : Type*} [Fintype V] [DecidableEq V] (G : V → V → Prop) [DecidableRel G]

/-- The exact three-hub retained-vertex budget sufficient for free13.
The sole imported Ramsey input is the explicit published R(3,10)≤41
assertion, via the known K4-free free10 theorem for the retained pool. -/
theorem free13_of_three_hub_budget
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a)
    (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (x w y : V) (hxw : G x w) (hwy : G w y) (hxy : ¬ G x y) (xyne : x ≠ y)
    (Nxw : ¬ Lone G x w) (Nyw : ¬ Lone G y w)
    (A B : Finset V)
    (hA : ∀ a ∈ A, CenterEligible G x w y a)
    (hB : ∀ a ∈ B, OuterEligible G x w y a)
    (iA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b)
    (iB : ∀ a ∈ B, ∀ b ∈ B, ¬ pairConflict G x y a b)
    (hSub : A ∪ B ⊆ ((neighbors G x ∪ neighbors G y) ∪ neighbors G w) \
      ({x,w,y} : Finset V))
    (budget : (neighbors G x).card + (neighbors G y).card + (neighbors G w).card + 40 ≤
       Fintype.card V + (neighbors G x ∩ neighbors G w).card +
       (neighbors G y ∩ neighbors G w).card +
       ((neighbors G x ∩ neighbors G y) \ insert w (neighbors G w)).card +
       (A ∪ B).card) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  let H : Finset V := {x,w,y}
  let U0 := (neighbors G x ∪ neighbors G y) ∪ neighbors G w
  let U := U0 \ H
  let K := A ∪ B
  let Del := U \ K
  let R : Finset V := Finset.univ \ (H ∪ Del)
  have xwne : x ≠ w := fun e => irr _ (e ▸ hxw)
  have wyne : w ≠ y := fun e => irr _ (e ▸ hwy)
  have hH : H.card = 3 := by
    simp [H,xwne,xyne,wyne,Finset.card_insert_of_notMem]
  have hc := three_hub_external_union G sym irr x w y hxw hwy xwne xyne wyne
  change U.card + (neighbors G x∩neighbors G w).card +
    (neighbors G y∩neighbors G w).card +
    ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card+4 =
    (neighbors G x).card + (neighbors G y).card + (neighbors G w).card at hc
  have hD := Finset.card_sdiff_add_card_eq_card hSub
  change Del.card + K.card = U.card at hD
  have hDis : Disjoint H Del := by
    apply Finset.disjoint_left.mpr
    intro u hu hd
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hd).1).2 hu
  have hR := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (H ∪ Del))
  change R.card + (H ∪ Del).card = Finset.univ.card at hR
  rw [Finset.card_union_of_disjoint hDis, hH, Finset.card_univ] at hR
  have rsize : 41 ≤ R.card := by
    change _ ≤ _ + K.card at budget
    omega
  obtain ⟨T,subT,Tsize,Tfree⟩ := Erdős151.H12.large_pool_free_ten (G := G) sym irr link R41 R rsize
  have hHT : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro u hu ut
    exact (Finset.mem_sdiff.mp (subT ut)).2 (Finset.mem_union_left _ hu)
  refine ⟨H ∪ T, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hHT,hH]
    omega
  · rw [Finset.coe_union]
    apply safe_insert_induced_path G sym irr x w y hxy Nxw Nyw (A : Set V) (B : Set V) _
      hA hB iA iB Tfree
    intro q hq
    have nr := (Finset.mem_sdiff.mp (subT hq)).2
    by_cases hK : q ∈ K
    · exact (Finset.mem_union.mp hK).elim Or.inl (fun h => Or.inr (Or.inl h))
    · right
      right
      have nU : q ∉ U0 := by
        intro h0
        have nh : q ∉ H := fun h => nr (Finset.mem_union_left _ h)
        apply nr
        apply Finset.mem_union_right
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h0,nh⟩,hK⟩
      exact ⟨fun e => nU (Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_neighbors G).mpr e))),
        fun e => nU (Finset.mem_union_right _ ((mem_neighbors G).mpr e)),
        fun e => nU (Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_neighbors G).mpr e)))⟩

#print axioms free13_of_three_hub_budget
end Erdos151H13
