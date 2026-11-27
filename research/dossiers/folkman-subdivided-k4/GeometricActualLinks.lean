import GeometricLinkMargin

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def rootedTriangles (g : EdgeGraph V) (v : V) : Finset (EdgeGraph V) :=
  (triangles g).filter (fun T => v∈triVertices T)

noncomputable def rootedLinkEdges (g : EdgeGraph V) (v : V) : EdgeGraph V :=
  (rootedTriangles g v).image (fun T => (triVertices T).erase v)

theorem triangle_edges_from_vertices {T : EdgeGraph V} (sh : triangleShape T) :
    T=(triVertices T).powersetCard 2 := by
  obtain ⟨a,b,c,ab,ac,bc,rfl⟩ := sh
  rw [triple_vertices_exact,powerset_two_triple ab ac bc]

theorem rootedLink_image_injective (g : EdgeGraph V) (v : V) :
    Set.InjOn (fun T : EdgeGraph V => (triVertices T).erase v) (rootedTriangles g v) := by
  intro A a B b h
  obtain ⟨ta,va⟩ := mem_filter.mp a
  obtain ⟨tb,vb⟩ := mem_filter.mp b
  rw [triangle_edges_from_vertices (mem_triangles.mp ta).2,
    triangle_edges_from_vertices (mem_triangles.mp tb).2]
  congr 1
  change (triVertices A).erase v = (triVertices B).erase v at h
  rw [← Finset.insert_erase va, ← Finset.insert_erase vb,h]

theorem rootedLink_count (g : EdgeGraph V) (v : V) :
    ((rootedLinkEdges g v).card:ℝ)=linkTriangleCount g v := by
  unfold rootedLinkEdges linkTriangleCount rootIncidence
  rw [Finset.card_image_of_injOn (rootedLink_image_injective g v),← Finset.sum_filter]
  simp [rootedTriangles]

theorem rootedLinkEdge_iff (g : EdgeGraph V) (v x y : V) (xy : x≠y) :
    ({x,y}:Finset V)∈rootedLinkEdges g v ↔
      hasEdge g v x ∧ hasEdge g v y ∧ hasEdge g x y := by
  constructor
  · intro h
    obtain ⟨T,mt,pair⟩ := mem_image.mp h
    obtain ⟨tr,rt⟩ := mem_filter.mp mt
    have vx : v≠x := by
      intro e
      have h' : v∈(triVertices T).erase v := pair.symm ▸ (by simp [e] : v∈({x,y}:Finset V))
      exact (Finset.mem_erase.mp h').1 rfl
    have vy : v≠y := by
      intro e
      have h' : v∈(triVertices T).erase v := pair.symm ▸ (by simp [e] : v∈({x,y}:Finset V))
      exact (Finset.mem_erase.mp h').1 rfl
    have vertices : triVertices T={v,x,y} := by rw [←Finset.insert_erase rt,pair]
    have eq : T=triangleEdges v x y := by
      rw [triangle_edges_from_vertices (mem_triangles.mp tr).2,vertices,powerset_two_triple vx vy xy]
    have sub := (mem_triangles.mp tr).1
    rw [eq] at sub
    exact ⟨⟨vx,sub (by simp [triangleEdges])⟩,⟨vy,sub (by simp [triangleEdges])⟩,
      ⟨xy,sub (by simp [triangleEdges])⟩⟩
  · rintro ⟨⟨vx,hx⟩,⟨vy,hy⟩,⟨_,hz⟩⟩
    refine mem_image.mpr ⟨triangleEdges v x y,mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · exact mem_triangles.mpr ⟨by simp [triangleEdges,Finset.insert_subset_iff,hx,hy,hz],
        ⟨v,x,y,vx,vy,xy,rfl⟩⟩
    · simp [triple_vertices_exact]
    · rw [triple_vertices_exact,Finset.erase_insert (by simp [vx,vy])]

#print axioms rootedLinkEdge_iff
end RobustFolkman.GeometricGap
