import GeometricPairGraphs
import GeometricSampleCut

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped InnerProductSpace ENNReal
variable {I J S E : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def liftEdges (e : I↪J) (G : EdgeGraph I) : EdgeGraph J :=
  G.map ⟨Finset.map e,Finset.map_injective e⟩

theorem liftEdges_card (e : I↪J) (G : EdgeGraph I) : (liftEdges e G).card=G.card := Finset.card_map _

theorem mono_map_embed (e : I↪J) (b : J→Bool) (s : Finset I) :
    Monochrom b (s.map e) ↔ Monochrom (b ∘ e) s := by
  constructor
  · intro h i hi j hj
    exact h (e i) (Finset.mem_map.2 ⟨i,hi,rfl⟩) (e j) (Finset.mem_map.2 ⟨j,hj,rfl⟩)
  · intro h i hi j hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨b',hb,rfl⟩ := Finset.mem_map.1 hj
    exact h a ha b' hb

theorem liftEdges_cut (e : I↪J) (G : EdgeGraph I) (b : J→Bool) :
    cutCount (liftEdges e G) b=cutCount G (b∘e) := by
  classical
  unfold liftEdges cutCount
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Function.Embedding.coeFn_mk,mono_map_embed]

/-- The set of tight edges on the original labels is the isomorphic image
of the cap graph on the retained label subtype. -/
theorem band_tight_graph_lift (A : Set S) (f : S→UnitSphere E) (t : ℝ) (x : J→S)
    (L : Finset J) (hL : ∀ i, i∈L ↔ x i∈A) :
    let K : Set (S×S) := {p | p.1∈A ∧ p.2∈A ∧ t≤⟪(f p.1).val,(f p.2).val⟫_ℝ}
    samplePredicateGraph K x =
      liftEdges (Function.Embedding.subtype (fun i => i∈L))
        (pointGraph t (fun i : {i : J // i∈L} => f (x i.val))) := by
  classical
  intro K
  ext T
  rw [samplePredicate_edge_eq]
  unfold liftEdges
  rw [Finset.mem_map]
  constructor
  · rintro ⟨i,j,ne,⟨hi,hj,tt⟩,eq⟩
    let i' : {i : J // i∈L} := ⟨i,(hL i).2 hi⟩
    let j' : {i : J // i∈L} := ⟨j,(hL j).2 hj⟩
    have nn : i'≠j' := fun h => ne (congrArg Subtype.val h)
    refine ⟨{i',j'},(pointGraph_pair t _ nn).2 tt,?_⟩
    simp only [Function.Embedding.coeFn_mk,map_insert,map_singleton]
    exact eq
  · rintro ⟨s,hs,hT⟩
    unfold pointGraph at hs
    rcases Finset.mem_image.1 hs with ⟨⟨i,j⟩,hh,rfl⟩
    have z := (Finset.mem_filter.1 hh).2
    refine ⟨i.val,j.val,fun e => z.1 (Subtype.ext e),⟨(hL _).1 i.property,(hL _).1 j.property,z.2⟩,?_⟩
    simp only [Function.Embedding.coeFn_mk,map_insert,map_singleton] at hT
    change ({i.val,j.val}:Finset J)=T at hT
    exact hT

#print axioms band_tight_graph_lift
#print axioms liftEdges_cut
end RobustFolkman.GeometricGap
