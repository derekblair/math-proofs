import UnblockingPools
import UpperIncidence

namespace Erdős151
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lone_symm {G : V → V → Prop} (sym : ∀ {a b}, G a b → G b a)
    {a b : V} (h : Lone G a b) : Lone G b a :=
  ⟨sym h.1, fun x hx => h.2 x hx.symm⟩

theorem sub_incidence {G : V → V → Prop} [DecidableRel G] [DecidableRel (Lone G)]
    (sym : ∀ {a b}, G a b → G b a) (S E X : Finset V) (sub : E ⊆ X) :
    (∑ x ∈ E, (ns (G := G) S x).card) ≤ Upper.incidence G S X ∧
    (∑ x ∈ E, (ls (G := G) S x).card) ≤ Upper.incidence (Lone G) S X := by
  classical
  have hn (x : V) : ns (G := G) S x = S.filter (fun u => G u x) := by
    ext u
    simp only [mem_ns, Support, Set.mem_setOf_eq, Finset.mem_filter]
    exact and_congr_right (fun _ => ⟨sym,sym⟩)
  have hl (x : V) : ls (G := G) S x = S.filter (fun u => Lone G u x) := by
    ext u
    simp only [mem_ls, Finset.mem_filter]
    exact and_congr_right (fun _ => ⟨lone_symm (G := G) sym,lone_symm (G := G) sym⟩)
  constructor
  · simp only [hn, Upper.incidence]
    exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
  · simp only [hl, Upper.incidence]
    exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)

theorem exterior_card (S : Finset V) (w : V) (hw : w ∉ S) :
    (Upper.ext S w).card = Fintype.card V - (S.card+1) := by
  unfold Upper.ext
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_insert_of_notMem hw]

theorem neighborhood_cap {G : V → V → Prop} [DecidableRel G]
    (sym : ∀ {a b}, G a b → G b a) (link : TriangleFreeLinks G)
    (cap : FreeCap G 10) (w : V) : (Upper.nbr G w).card ≤ 10 := by
  apply cap
  have hSet : (↑(Upper.nbr G w) : Set V) = {u | G w u} := by
    ext u
    simp [Upper.nbr]
  rw [hSet]
  exact neighborhood_free G sym link w

#print axioms sub_incidence
#print axioms exterior_card
#print axioms neighborhood_cap
end Erdős151
