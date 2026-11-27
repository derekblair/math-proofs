import GeometricActualLinks

namespace RobustFolkman.GeometricGap
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def rootedLinkCut (g : EdgeGraph V) (v : V) (b : V→Bool) : ℝ := by
  classical
  exact ∑ e∈rootedLinkEdges g v, if Monochrom b e then 0 else 1

theorem rootedLink_root_flag (T : EdgeGraph V) (v : V) (sh : triangleShape T)
    (rt : v∈triVertices T) (c : Finset V→Bool) :
    rootMixed T c v =
      if Monochrom (fun w => c {v,w}) ((triVertices T).erase v) then 0 else 1 := by
  classical
  obtain ⟨a,b,d,ab,ad,bd,rfl⟩ := sh
  obtain ⟨ha,hb,hd⟩ := incident_triplet a b d ab ad bd
  simp only [triple_vertices_exact,mem_insert,mem_singleton] at rt
  rcases rt with h|h|h
  · subst v
    have ea : ({a,b,d}:Finset V).erase a={b,d} := by ext w; simp; grind
    rw [rootMixed,triple_vertices_exact,ha,ea]
    simp [mono_two_iff]
  · subst v
    have eb : ({a,b,d}:Finset V).erase b={a,d} := by ext w; simp; grind
    rw [rootMixed,triple_vertices_exact,hb,eb]
    simp [mono_two_iff,Finset.pair_comm]
  · subst v
    have ed : ({a,b,d}:Finset V).erase d={a,b} := by ext w; simp; grind
    rw [rootMixed,triple_vertices_exact,hd,ed]
    simp [mono_two_iff,Finset.pair_comm]

theorem rootedLinkCut_count (g : EdgeGraph V) (v : V) (c : Finset V→Bool) :
    rootedLinkCut g v (fun w => c {v,w}) = linkMixedCount g c v := by
  classical
  unfold rootedLinkCut rootedLinkEdges
  rw [Finset.sum_image (rootedLink_image_injective g v)]
  unfold linkMixedCount
  symm
  calc
    _ = ∑ T∈rootedTriangles g v, rootMixed T c v := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro T ht hn
      have nh : v∉triVertices T := fun hv => hn (mem_filter.mpr ⟨ht,hv⟩)
      simp [rootMixed,nh]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T ht
      exact rootedLink_root_flag T v (mem_triangles.mp (mem_filter.mp ht).1).2 (mem_filter.mp ht).2 c

theorem margin_from_actual_link_maxcut (g : EdgeGraph V) (ρ : ℝ)
    (cap : ∀ (v : V) (b : V→Bool),
      rootedLinkCut g v b ≤ ((1+ρ)/2)*((rootedLinkEdges g v).card:ℝ)) :
    coloringMargin ((1-3*ρ)/4) g=true := by
  apply monochromatic_margin_from_link_cut
  intro v c
  rw [← rootedLinkCut_count,← rootedLink_count]
  exact cap v _

#print axioms margin_from_actual_link_maxcut
end RobustFolkman.GeometricGap
