import SimpleWagnerColor

namespace Erdős151.H13
open Erdős151.H12 Erdős151.H12.Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Lk (G : SimpleGraph V) (v : V) := {x : V // G.Adj v x}

noncomputable def actualSpoke (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (x : Lk G v) :
    Edges G := pairEdge G x.property

theorem spoke_set (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (x : Lk G v) :
    edgeRost G (actualSpoke G v x) = ({v,x.val} : Finset V) := rfl

theorem spoke_of_mem (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (e : Edges G)
    (he : v ∈ edgeRost G e) : ∃ x : Lk G v, actualSpoke G v x = e := by
  have card : (edgeRost G e).card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  obtain ⟨x,y,xy,eq⟩ := Finset.card_eq_two.mp card
  have hd : G.Adj x y := (host_iff_of_ne G xy).mp
    ⟨e,by rw [eq];simp,by rw [eq];simp⟩
  rw [eq] at he
  rcases Finset.mem_insert.mp he with rfl|hy
  · exact ⟨⟨y,hd⟩,(edgeRost G).injective ((spoke_set G v ⟨y,hd⟩).trans eq.symm)⟩
  · have ey : v=y := by simpa using hy
    subst v
    refine ⟨⟨x,hd.symm⟩,(edgeRost G).injective ?_⟩
    rw [spoke_set,eq,Finset.pair_comm]

/-- Actual graph local link cuts lift to the abstract Hall obstruction.
No uniform link type or Wagner identification is needed. -/
theorem actual_local_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (cut : ∀ v : V, ∀ U : Finset (Lk G v), U.Nonempty → (∃ j, j∉U) →
      3 ≤ ((U ×ˢ (Finset.univ\U)).filter (fun a => G.Adj a.1.val a.2.val)).card) :
    localSplit (edgeRost G) (triRost G) := by
  classical
  intro S v h
  obtain ⟨e,he,f,hf,hve,hvf⟩ := h
  obtain ⟨i,hi⟩ := spoke_of_mem G v e hve
  obtain ⟨j,hj⟩ := spoke_of_mem G v f hvf
  let U := (Finset.univ : Finset (Lk G v)).filter (fun i => actualSpoke G v i∈S)
  have hiU : i∈U := by simp [U,hi,he]
  have hjU : j∉U := by simp [U,hj,hf]
  let D := (U ×ˢ (Finset.univ\U)).filter (fun a : Lk G v × Lk G v => G.Adj a.1.val a.2.val)
  have Dcard := cut v U ⟨i,hiU⟩ ⟨j,hjU⟩
  change 3 ≤ D.card at Dcard
  let tri (a : ↥D) : Triangles G :=
    triangleNode G a.val.1.property (Finset.mem_filter.mp a.property).2 a.val.2.property
  have triSet (a : ↥D) : triRost G (tri a) = {v,a.val.1.val,a.val.2.val} := rfl
  have part1 (a : ↥D) : a.val.1 ∈ U := (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1
  have part2 (a : ↥D) : a.val.2 ∉ U :=
    (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).2).2
  have inj : Function.Injective tri := by
    intro a b h
    have eq := congrArg (triRost G) h
    rw [triSet,triSet] at eq
    have h1 : a.val.1.val ∈ ({v,b.val.1.val,b.val.2.val} : Finset V) := by rw [←eq];simp
    have h2 : a.val.2.val ∈ ({v,b.val.1.val,b.val.2.val} : Finset V) := by rw [←eq];simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at h1 h2
    have q1 : a.val.1=b.val.1 := by
      rcases h1 with h|h|h
      · exact (a.val.1.property.ne h.symm).elim
      · exact Subtype.ext h
      · exact (part2 b ((Subtype.ext h : a.val.1=b.val.2) ▸ part1 a)).elim
    have q2 : a.val.2=b.val.2 := by
      rcases h2 with h|h|h
      · exact (a.val.2.property.ne h.symm).elim
      · exact (part2 a ((Subtype.ext h : a.val.2=b.val.1).symm ▸ part1 b)).elim
      · exact Subtype.ext h
    exact Subtype.ext (Prod.ext q1 q2)
  let J : Finset (Triangles G) := (Finset.univ : Finset ↥D).map ⟨tri,inj⟩
  refine ⟨J,by simpa [J] using Dcard,?_⟩
  intro t ht
  obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp ht
  have ina : actualSpoke G v a.val.1 ∈ S := (Finset.mem_filter.mp (part1 a)).2
  have outb : actualSpoke G v a.val.2 ∉ S := fun h =>
    part2 a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  refine ⟨_,ina,_,outb,?_,?_,?_,?_⟩
  · rw [spoke_set];simp
  · rw [spoke_set];simp
  · simp only [Function.Embedding.coeFn_mk]
    rw [spoke_set,triSet]
    intro x h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
    exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
  · simp only [Function.Embedding.coeFn_mk]
    rw [spoke_set,triSet]
    intro x h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
    exact h.elim Or.inl (fun h => Or.inr (Or.inr h))

#print axioms actual_local_split
end Erdős151.H13
