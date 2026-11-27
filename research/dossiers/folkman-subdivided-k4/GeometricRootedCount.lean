import GeometricWeightedFailure

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

def rootedTriples (v : V) : Finset (Finset V) :=
  ((univ : Finset V).powersetCard 3).filter (fun s => v∈s)

theorem rootedTriples_erase (v : V) :
    (rootedTriples v).image (fun s => s.erase v) =
      ((univ : Finset V).erase v).powersetCard 2 := by
  ext s
  rw [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h3, hv⟩ := Finset.mem_filter.mp ha
    refine ⟨?_,?_⟩
    · intro j hj
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem hv,(Finset.mem_powersetCard.mp h3).2]
  · rintro ⟨hs, h2⟩
    have hv : v ∉ s := fun h => (Finset.mem_erase.mp (hs h)).1 rfl
    refine ⟨insert v s,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,?_⟩,Finset.mem_insert_self _ _⟩,?_⟩
    · rw [Finset.card_insert_of_notMem hv,h2]
    · simp [Finset.erase_insert hv]

theorem rootedTriples_card (v : V) :
    (rootedTriples v).card = (Fintype.card V-1).choose 2 := by
  have hinj : Set.InjOn (fun s : Finset V => s.erase v) (↑(rootedTriples v) : Set (Finset V)) := by
    intro a ha b hb eq
    have av : v∈a := (Finset.mem_filter.mp ha).2
    have bv : v∈b := (Finset.mem_filter.mp hb).2
    simpa only [insert_erase av,insert_erase bv] using congrArg (insert v) eq
  rw [←Finset.card_image_of_injOn hinj,rootedTriples_erase,Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ v),Finset.card_univ]

theorem linkTriangleCount_indicator (g : EdgeGraph V) (v : V) :
    linkTriangleCount g v = ∑ s ∈ rootedTriples v, triangleIndicator g s := by
  classical
  have hinj : Set.InjOn (fun s : Finset V => s.powersetCard 2) (↑(tripleTriangles g) : Set (Finset V)) := by
    intro s hs t ht eq
    have hs3 := (mem_powersetCard.mp (mem_filter.mp (show s∈tripleTriangles g from hs)).1).2
    have ht3 := (mem_powersetCard.mp (mem_filter.mp (show t∈tripleTriangles g from ht)).1).2
    exact (triple_vertices s hs3).symm.trans
      ((congrArg (fun X : Finset (Finset V) => X.biUnion id) eq).trans (triple_vertices t ht3))
  unfold linkTriangleCount
  rw [triangles_image,Finset.sum_image hinj]
  have hs : ∀ s ∈ tripleTriangles g, rootIncidence (s.powersetCard 2) v = if v∈s then 1 else 0 := by
    intro s hm
    unfold rootIncidence triVertices
    rw [triple_vertices s ((mem_powersetCard.mp (mem_filter.mp hm).1).2)]
  rw [Finset.sum_congr rfl hs]
  unfold tripleTriangles rootedTriples
  rw [Finset.sum_filter]
  simp_rw [triangleIndicator,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases a : s.powersetCard 2 ⊆ g <;> by_cases b : v∈s <;> simp [a,b]

#print axioms linkTriangleCount_indicator
#print axioms rootedTriples_card
end RobustFolkman.GeometricGap
