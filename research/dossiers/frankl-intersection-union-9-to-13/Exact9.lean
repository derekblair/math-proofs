import Complete9
namespace IU
set_option maxRecDepth 15000
set_option maxHeartbeats 0

def construction9 : List Bag := [{0,1,2},{0,1,3},{0,2,3},{1,2,3},{0,1,2,3},{0,1,2,4},{0,1,3,4},{0,2,3,4},{1,2,3,4},{0,1,2,3,4},{0,1,2,5},{0,1,3,5},{0,2,3,5},{1,2,3,5},{0,1,2,3,5},{0,1,2,4,5},{0,1,3,4,5},{0,2,3,4,5},{1,2,3,4,5},{0,1,2,3,4,5},{0,1,2,6},{0,1,3,6},{0,2,3,6},{1,2,3,6},{0,1,2,3,6},{0,1,2,4,6},{0,1,3,4,6},{0,2,3,4,6},{1,2,3,4,6},{0,1,2,3,4,6},{0,1,2,7},{0,1,3,7},{0,2,3,7},{1,2,3,7},{0,1,2,3,7},{0,1,2,4,7},{0,1,3,4,7},{0,2,3,4,7},{1,2,3,4,7},{0,1,2,3,4,7},{0,1,2,8},{0,1,3,8},{0,2,3,8},{1,2,3,8},{0,1,2,3,8},{0,1,2,4,8},{0,1,3,4,8},{0,2,3,4,8},{1,2,3,4,8},{0,1,2,3,4,8}]
private theorem size9 : construction9.Nodup ∧ construction9.length=50 := by decide +kernel
private theorem range9 : ∀ A∈construction9, A ⊆ Finset.range 9 := by decide +kernel
private theorem pair9 :
    ∀ A∈construction9, ∀ B∈construction9, 2≤(A∩B).card ∧ (A∪B).card≤9-2 := by
  decide +kernel

theorem attain_9_2_2 : ∃ F : Sys, IsIU F 9 2 2 ∧ F.card=50 := by
  refine ⟨construction9.toFinset,⟨?_,?_⟩,?_⟩
  · intro A a
    exact range9 A (List.mem_toFinset.mp a)
  · intro A a B b
    exact pair9 A (List.mem_toFinset.mp a) B (List.mem_toFinset.mp b)
  · rw [List.toFinset_card_of_nodup size9.1,size9.2]

/-- Exact nine-coordinate parameter case of the intersection–union product problem:
a largest family on nine coordinates, with pairwise intersections at least two
and unions at most seven, has exactly fifty members. -/
theorem intersection_union_9_2_2 :
    (∀ F : Sys, IsIU F 9 2 2 → F.card≤50) ∧ ∃ F : Sys, IsIU F 9 2 2 ∧ F.card=50 :=
  ⟨upper_bound_9_2_2,attain_9_2_2⟩

#print axioms intersection_union_9_2_2
end IU
