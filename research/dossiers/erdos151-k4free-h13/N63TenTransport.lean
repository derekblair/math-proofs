import N63TenRightPool
import N63FiveMatchCore

namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

def TenWitness : Prop :=
  ∃ (x y : V) (S : Finset V), x≠y ∧ ¬G x y ∧
    (∀ z∈S, z≠x ∧ z≠y ∧ ¬G x z ∧ ¬G y z) ∧
    Erdos151Ramsey.Independent G S ∧ priceOK 10 (fullDeg G x) (fullDeg G y) S.card

theorem hostDegree_of_rows {n : Nat} (r : Array Nat) (e : Fin n ≃ V)
    (adjE : ∀ i j : Fin n, adj r i.val j.val = true ↔ G (e i) (e j)) (i : Fin n) :
    deg r n i.val = fullDeg G (e i) := by
  unfold deg
  rw [← finRange_vals, List.filter_map, List.length_map, list_filter_count_sum]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
  have de : fullDeg G (e i) = ∑ j : V, if G (e i) j then 1 else 0 := by
    rw [fullDeg,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [de]
  apply Finset.sum_equiv e (by simp)
  intro j _
  exact if_congr (adjE i j) rfl rfl

theorem chart_to_ten_witness (P : TenPivotEntry) (cert : P.cert) (e : Fin 10 ≃ V)
    (adjE : ∀ i j : Fin 10, adj P.rows i.val j.val = true ↔ G (e i) (e j)) :
    TenWitness G := by
  classical
  obtain ⟨⟨hx,hy,hn,had,hd,hS,hi⟩,hp⟩ := cert
  let X : Fin 10 := ⟨P.x,hx⟩
  let Y : Fin 10 := ⟨P.y,hy⟩
  let F := Finset.univ.filter (fun i : Fin 10 => i.val ∈ P.center)
  let S := F.map e.toEmbedding
  have cf : F.map Fin.valEmbedding = P.center.toFinset := by
    ext z
    simp only [F,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro h
      exact ⟨⟨z,(hS z h).1⟩,h,rfl⟩
  have hCard : S.card=P.center.length := by
    rw [Finset.card_map,←Finset.card_map Fin.valEmbedding,cf,List.toFinset_card_of_nodup hd]
  have hXY : e X≠e Y := fun h => hn (congrArg Fin.val (e.injective h))
  have hNx : ¬G (e X) (e Y) := fun h => by
    have h := (adjE X Y).mpr h
    rw [had] at h
    contradiction
  refine ⟨e X,e Y,S,hXY,hNx,?_,?_,?_⟩
  · intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
    have hmem := (Finset.mem_filter.mp hj).2
    obtain ⟨_,hneX,hneY,hax,hay⟩ := hS j.val hmem
    exact ⟨fun h => hneX (congrArg Fin.val (e.injective h)),
      fun h => hneY (congrArg Fin.val (e.injective h)),
      fun h => Bool.false_ne_true (hax.symm.trans ((adjE X j).mpr h)),
      fun h => Bool.false_ne_true (hay.symm.trans ((adjE Y j).mpr h))⟩
  · intro a ha b hb h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hb
    exact Bool.false_ne_true ((hi j.val (Finset.mem_filter.mp hj).2 k.val
      (Finset.mem_filter.mp hk).2).symm.trans ((adjE j k).mpr h))
  · rw [hCard,←hostDegree_of_rows G P.rows e adjE X,←hostDegree_of_rows G P.rows e adjE Y]
    exact hp

theorem witness_right_pool (w : V) {q : Nat} (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z})
    (y : Fin q) (S : Finset (Fin q))
    (hS : S ⊆ rightPool G (fun j => (R j).val) y)
    (hI : Erdos151Ramsey.Independent (fun a b => G (R a).val (R b).val) S)
    (hP : priceOK 10 (fullDeg G w) (fullDeg G (R y).val) S.card) :
    TenWitness G := by
  let e : Fin q ↪ V := ⟨fun j => (R j).val,Subtype.val_injective.comp R.injective⟩
  refine ⟨w,(R y).val,S.map e,(R y).property.1.symm,(R y).property.2,?_,?_,?_⟩
  · intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨hn,hN⟩ := Finset.mem_filter.mp (hS hj)
    exact ⟨(R j).property.1,fun he => (Finset.mem_erase.mp hn).1 (e.injective he),(R j).property.2,hN⟩
  · intro a ha b hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hb
    exact hI j hj k hk
  · simpa using hP

#print axioms chart_to_ten_witness
#print axioms witness_right_pool
end Erdos151N63
