import DyckSets
namespace FussCover
open Finset

lemma prefix_le_card {n : ℕ} (S : Finset (Fin n)) (q : ℕ) :
    prefixCard S q ≤ S.card := Finset.card_filter_le _ _

lemma prefix_order {n j : ℕ} (S : Finset (Fin n)) (hc : S.card=j) (q : ℕ) (i : Fin j) :
    i.val < prefixCard S q ↔ (S.orderEmbOfFin hc i).val<q := by
  classical
  have eq : (Finset.univ.filter (fun a : Fin j => (S.orderEmbOfFin hc a).val<q)).card =
      prefixCard S q := by
    unfold prefixCard
    calc
      _ = ((Finset.univ.map (S.orderEmbOfFin hc).toEmbedding).filter fun a => a.val<q).card := by
        rw [Finset.filter_map,Finset.card_map]
        rfl
      _ = _ := by rw [Finset.map_orderEmbOfFin_univ S hc]
  rw [←eq]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b h hq
  have le := (S.orderEmbOfFin hc).monotone h
  change (S.orderEmbOfFin hc b).val ≤ (S.orderEmbOfFin hc a).val at le
  exact lt_of_le_of_lt le hq

lemma ballot_iff_orders {j : ℕ} (S : Finset (Fin (2*j))) (hc : S.card=j) :
    (∀ q, prefixCard Sᶜ q ≤ prefixCard S q) ↔
    ∀ i : Fin j, S.orderEmbOfFin hc i < (Sᶜ : Finset _).orderEmbOfFin (comp_card S hc) i := by
  let U := S.orderEmbOfFin hc
  let D := (Sᶜ : Finset _).orderEmbOfFin (comp_card S hc)
  constructor
  · intro H i
    let q := (D i).val+1
    have hasD : i.val < prefixCard Sᶜ q := (prefix_order _ (comp_card S hc) q i).mpr (by dsimp [q,D]; omega)
    have hasU := (prefix_order _ hc q i).mp (lt_of_lt_of_le hasD (H q))
    have le : U i ≤ D i := by change (U i).val ≤ (D i).val; change (U i).val<(D i).val+1 at hasU; omega
    have ne : U i ≠ D i := by
      intro eq
      have a := S.orderEmbOfFin_mem hc i
      have b := (Sᶜ : Finset _).orderEmbOfFin_mem (comp_card S hc) i
      change U i ∈ S at a
      change D i ∈ Sᶜ at b
      exact (Finset.mem_compl.mp b) (eq ▸ a)
    exact lt_of_le_of_ne le ne
  · intro H q
    by_cases hz : prefixCard Sᶜ q=0
    · omega
    let i : Fin j := ⟨prefixCard Sᶜ q-1, by
      have e := prefix_le_card (Sᶜ : Finset _) q
      rw [comp_card S hc] at e
      omega⟩
    have did : i.val < prefixCard Sᶜ q := by change prefixCard Sᶜ q-1<prefixCard Sᶜ q; omega
    have lessD := (prefix_order _ (comp_card S hc) q i).mp did
    change (D i).val<q at lessD
    have less : (U i).val<(D i).val := H i
    have moreU := (prefix_order _ hc q i).mpr (lt_trans less lessD)
    change prefixCard Sᶜ q-1<prefixCard S q at moreU
    omega

end FussCover
