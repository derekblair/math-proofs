import Density
import GraphBits

open scoped BigOperators

namespace QuorumMinimum

noncomputable def presentEquiv {A : Type} (p : EdgeSlot A → Bool) :
    (bitGraph p).edgeSet ≃ {e : EdgeSlot A // p e = true} where
  toFun e := by
    have hh := e.property
    change e.val ∈ (SimpleGraph.fromEdgeSet {x | ∃ h : ¬x.IsDiag, p ⟨x,h⟩=true}).edgeSet at hh
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
    refine ⟨⟨e.val,(bitGraph p).not_isDiag_of_mem_edgeSet e.property⟩,?_⟩
    obtain ⟨⟨_,hval⟩,_⟩ := hh
    exact hval
  invFun e := by
    refine ⟨e.val.val,?_⟩
    rw [bitGraph,SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨e.val.property,e.property⟩,e.val.property⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext (Subtype.ext rfl)

theorem ec_bitGraph {A : Type} [Fintype A] [DecidableEq A] (p : EdgeSlot A → Bool) :
    ec (bitGraph p)= ∑ e : EdgeSlot A, if p e then 1 else 0 := by
  classical
  change Nat.card (bitGraph p).edgeSet = _
  rw [Nat.card_congr (presentEquiv p), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole]
  rfl

theorem bitGraph_comap {A B : Type} (u : A ↪ B) (p : EdgeSlot B → Bool) :
    (bitGraph p).comap u = bitGraph (p ∘ edgeSlots u) := by
  ext x y
  by_cases h : x=y
  · subst y; simp
  · rw [SimpleGraph.comap_adj,bitGraph_adj _ (fun eq => h (u.injective eq)),bitGraph_adj _ h]
    rfl

theorem zeros_sum_flip {n : Nat} (f : Fin n → Bool) :
    zeros f+zeros (flip f)=n := by
  unfold zeros
  rw [←Finset.sum_add_distrib]
  have h (i : Fin n) : (if f i then (0:Nat) else 1)+(if flip f i then 0 else 1)=1 := by
    cases e : f i <;> simp [flip,e]
  simp [h]

theorem bit_edge_count {A : Type} [Fintype A] {k : Nat} (g : Fin k ≃ EdgeSlot A)
      (p : EdgeSlot A → Bool) : ec (bitGraph p)=zeros (flip (p ∘ g)) := by
  classical
  rw [ec_bitGraph,zeros,← g.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  cases e : p (g i) <;> simp [flip,e]

theorem dense_test_both (n L : Nat) (Lpos : 0<L) (nlim : n≤2^L) :
    let t := 32*L+1
    ∃ G : SimpleGraph (Fin n), ∀ u : Fin t ↪ Fin n,
      t*(t-1) ≤ 8*ec (G.comap u) ∧ t*(t-1) ≤ 8*ec (Gᶜ.comap u) := by
  classical
  let t := 32*L+1
  let r := 2*L*t
  let g : Fin (8*r) ≃ EdgeSlot (Fin t) := (Fintype.equivFinOfCardEq (slot_count L)).symm
  have hb : t*(t-1)=16*r := by
    have ht : t-1=32*L := by unfold t; omega
    rw [ht]; unfold r; ring
  obtain ⟨p,hp⟩ := test_set_bits n L Lpos nlim
  refine ⟨bitGraph p,fun u => ?_⟩
  have key (q : EdgeSlot (Fin n) → Bool)
      (hlow : zeros (q ∘ (g.toEmbedding.trans (edgeSlots u))) < 6*r) :
      t*(t-1) ≤ 8*ec ((bitGraph q).comap u) := by
    rw [bitGraph_comap,bit_edge_count g,hb]
    let a : Fin (8*r) → Bool := q ∘ (g.toEmbedding.trans (edgeSlots u))
    change zeros a < 6*r at hlow
    have hs := zeros_sum_flip a
    change 16*r ≤ 8*zeros (flip a)
    omega
  exact ⟨key p (hp u).1,by rw [←bitGraph_flip]; exact key (flip p) (hp u).2⟩

theorem all_from_fin_tests {V : Type} (G : SimpleGraph V) (t : Nat) (ht : 2≤t)
    (H : ∀ u : Fin t ↪ V, t*(t-1) ≤ 8*ec (G.comap u)) :
    ∀ (W : Type) [Fintype W] (u : W ↪ V), t≤Fintype.card W →
      Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap u) := by
  classical
  apply density_lift G t ht
  intro W _ u sz
  let q : Fin t ≃ W := (Fintype.equivFinOfCardEq sz).symm
  let v : Fin t ↪ V := q.toEmbedding.trans u
  have iso : (G.comap v) ≃g (G.comap u) := by
    change (G.comap u).comap q ≃g G.comap u
    exact SimpleGraph.Iso.comap q (G.comap u)
  have counts : ec (G.comap v)=ec (G.comap u) := by
    rw [ec_eq,ec_eq]
    exact iso.card_edgeFinset_eq
  rw [sz,←counts]
  exact H v

theorem dense_all_both (n L : Nat) (lp : 0<L) (nlim : n≤2^L) :
    ∃ G : SimpleGraph (Fin n), ∀ (W : Type) [Fintype W] (u : W ↪ Fin n),
      32*L+1≤Fintype.card W →
        Fintype.card W*(Fintype.card W-1) ≤ 8*ec (G.comap u) ∧
        Fintype.card W*(Fintype.card W-1) ≤ 8*ec (Gᶜ.comap u) := by
  obtain ⟨G,H⟩ := dense_test_both n L lp nlim
  have ht : 2≤32*L+1 := by omega
  exact ⟨G,fun W _ u hu =>
    ⟨all_from_fin_tests G _ ht (fun v => (H v).1) W u hu,
     all_from_fin_tests Gᶜ _ ht (fun v => (H v).2) W u hu⟩⟩

#print axioms dense_all_both
#print axioms dense_test_both

end QuorumMinimum
