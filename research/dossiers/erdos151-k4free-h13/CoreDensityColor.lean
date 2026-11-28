import CoreGraphDensity
import SeymourDensity

namespace Erdős151.H12
open Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Edges (G : SimpleGraph V) [DecidableRel G.Adj] := ↥(G.cliqueFinset 2)
abbrev Triangles (G : SimpleGraph V) [DecidableRel G.Adj] := ↥(G.cliqueFinset 3)
abbrev TriEdges (G : SimpleGraph V) [DecidableRel G.Adj] :=
  edgesIn (G.cliqueFinset 2) (G.cliqueFinset 3)

theorem pair_clique (G : SimpleGraph V) {a b : V} (h : G.Adj a b) :
    G.IsNClique 2 ({a,b} : Finset V) := by
  refine ⟨?_,by simp [h.ne]⟩
  intro x hx y hy ne
  simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> first
    | exact False.elim (ne rfl)
    | exact h
    | exact h.symm

def pairEdge (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (h : G.Adj a b) : Edges G :=
  ⟨{a,b},SimpleGraph.mem_cliqueFinset_iff.mpr (pair_clique G h)⟩

def triangleNode (G : SimpleGraph V) [DecidableRel G.Adj] {a b d : V}
    (ab : G.Adj a b) (bd : G.Adj b d) (ad : G.Adj a d) : Triangles G :=
  ⟨{a,b,d},SimpleGraph.mem_cliqueFinset_iff.mpr
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨ab,ad,bd⟩)⟩

private theorem card_edge (G : SimpleGraph V) [DecidableRel G.Adj] (e : Edges G) :
    e.val.card=2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq

private theorem triangle_pair_sets (p : Finset V) (a b c : V)
    (h : p.card=2) (hs : p⊆{a,b,c}) :
    p={a,b} ∨ p={b,c} ∨ p={a,c} := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp h
  have hx := hs (show x ∈ ({x,y} : Finset V) by simp)
  have hy := hs (show y ∈ ({x,y} : Finset V) by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    first | exact False.elim (hxy rfl)
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
          | exact Or.inl (Finset.pair_comm _ _)
          | exact Or.inr (Or.inl (Finset.pair_comm _ _))
          | exact Or.inr (Or.inr (Finset.pair_comm _ _))

theorem to_safe_of_mixed (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : Edges G → Bool) (hm : ∀ t, Mixed label (TriEdges G t)) :
    ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ BikovLocal.Safe G.Adj c := by
  classical
  let c (a b : V) : Bool := if h : G.Adj a b then label (pairEdge G h) else false
  have same (a b : V) : c a b=c b a := by
    by_cases h : G.Adj a b
    · simp only [c,dif_pos h,dif_pos h.symm]
      congr 1
      exact Subtype.ext (Finset.pair_comm _ _)
    · have hr : ¬ G.Adj b a := fun nh => h nh.symm
      simp [c,h,hr]
  refine ⟨c,same,?_⟩
  intro a b d ab bd da hh
  let t := triangleNode G ab bd da.symm
  let p := pairEdge G ab
  let q := pairEdge G bd
  let r := pairEdge G da.symm
  have hp : c a b=label p := by simp [c,ab,p]
  have hq : c b d=label q := by simp [c,bd,q]
  have hr : c d a=label r := by rw [same d a]; simp [c,da.symm,r]
  have hq' : label p=label q := hp.symm.trans (hh.1.trans hq)
  have hr' : label p=label r := hp.symm.trans (hh.1.trans (hh.2.trans hr))
  have all (s : Edges G) (hs : s∈TriEdges G t) : label s=label p := by
    have hsub : s.val ⊆ ({a,b,d}:Finset V) := (Finset.mem_filter.mp hs).2
    rcases triangle_pair_sets s.val a b d (card_edge G s) hsub with he|he|he
    · exact congrArg label (Subtype.ext he)
    · exact (congrArg label (show s=q from Subtype.ext he)).trans hq'.symm
    · exact (congrArg label (show s=r from Subtype.ext he)).trans hr'.symm
  obtain ⟨⟨u,hu,htu⟩,⟨v,hv,htv⟩⟩ := hm t
  have impossible : (true:Bool)=false := htu.symm.trans ((all u hu).trans ((all v hv).symm.trans htv))
  cases impossible

#print axioms pair_clique
#print axioms to_safe_of_mixed
end Erdős151.H12
