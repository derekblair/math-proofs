import WalkGraphPartition
import Mathlib.Data.List.Nodup

namespace IU.UniversalCount
open Finset IU.Universal

theorem vertex_nodup (s : Nat) : (vertexList s).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_flatMap.mpr
  constructor
  · intro r _
    apply List.nodup_flatMap.mpr
    constructor
    · intro w _
      apply List.Nodup.map _ List.nodup_range
      intro a b E
      exact congrArg (fun x : Vertex => x.2.2) E
    · apply List.Pairwise.imp _ List.nodup_range
      intro a b ne v ha hb
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨k,_,E⟩ := List.mem_map.mp hb
      exact ne (congrArg (fun x : Vertex => x.2.1) E).symm
  · apply List.Pairwise.imp _ List.nodup_range
    intro a b ne v ha hb
    obtain ⟨w,_,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨u,_,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,_,E⟩ := List.mem_map.mp hb
    exact ne (congrArg (fun x : Vertex => x.1) E).symm

noncomputable instance (s : Nat) : Fintype (BucketIndex s) := by
  let enc (i : BucketIndex s) : Fin (s+1) × Fin (s+1) × Fin (s+1) :=
    (⟨i.val.1,by have h:=i.property; change 2 * i.val.1 ≤ i.val.2.2 ∧ i.val.2.2 + 2 * i.val.2.1 ≤ s at h; omega⟩,
     ⟨i.val.2.1,by have h:=i.property; change 2 * i.val.1 ≤ i.val.2.2 ∧ i.val.2.2 + 2 * i.val.2.1 ≤ s at h; omega⟩,
     ⟨i.val.2.2,by have h:=i.property; change 2 * i.val.1 ≤ i.val.2.2 ∧ i.val.2.2 + 2 * i.val.2.1 ≤ s at h; omega⟩)
  apply Fintype.ofInjective enc
  intro a b E
  apply Subtype.ext
  exact congrArg (fun q : Fin (s+1) × Fin (s+1) × Fin (s+1) =>
     (q.1.val,q.2.1.val,q.2.2.val)) E

instance (s r z m : Nat) : Finite (GraphBucket s r z m) := by
  let enc (w : GraphBucket s r z m) : Fin (2^s) :=
    ⟨w.val, ((mem_vertices s r w.val (m-r+z)).mp w.property.1).2.1⟩
  exact Finite.of_injective enc (fun a b E => Subtype.ext (congrArg Fin.val E))

theorem vertexCount_sum (s : Nat) :
    (vertexList s).length =
      ∑ i : BucketIndex s, s.choose (min (i.val.2.2-2*i.val.1) (s-i.val.2.2-2*i.val.2.1)) := by
  classical
  have e : ∀ a : Vertex, a ∈ (vertexList s).toFinset ↔ a ∈ vertexList s := by simp
  letI : Fintype {v : Vertex // v∈vertexList s} := Fintype.ofFinset _ e
  calc
    (vertexList s).length = Nat.card {v : Vertex // v∈vertexList s} := by
      rw [Nat.card_eq_fintype_card]
      exact (List.toFinset_card_of_nodup (vertex_nodup s)).symm.trans
        (Fintype.card_ofFinset _ e).symm
    _ = Nat.card ((i : BucketIndex s) × GraphBucket s i.val.1 i.val.2.1 i.val.2.2) :=
      Nat.card_congr (graph_partition s)
    _ = _ := by
      rw [Nat.card_sigma]
      apply sum_congr rfl
      intro i _
      exact graph_bucket_card s i.val.1 i.val.2.1 i.val.2.2 i.property.1 i.property.2

#print axioms vertexCount_sum
end IU.UniversalCount
