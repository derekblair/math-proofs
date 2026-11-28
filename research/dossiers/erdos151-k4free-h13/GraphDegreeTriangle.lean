import MinimalTriangleDensity
import UnblockingExterior

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pair_edge_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V) (e : Finset V) (he : e∈G.cliqueFinset 2) (hw : w∈e) :
    ∃ x, G.Adj w x ∧ e={w,x} := by
  have h := SimpleGraph.mem_cliqueFinset_iff.mp he
  obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp h.card_eq
  have ad : G.Adj a b := h.isClique (by simp) (by simp) ab
  simp only [Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with rfl|rfl
  · exact ⟨b,ad,rfl⟩
  · exact ⟨a,ad.symm,Finset.pair_comm _ _⟩

theorem nbr_eq_incident_edges (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    (Upper.nbr G.Adj w).card = ((G.cliqueFinset 2).filter (fun e => w∈e)).card := by
  classical
  let S := Upper.nbr G.Adj w
  have adj (x : ↥S) : G.Adj w x.val := (Finset.mem_filter.mp x.property).2
  let f : ↥S ↪ Finset V :=
    ⟨fun x => {w,x.val},by
      intro x y h
      have hs : x.val∈({w,y.val}:Finset V) := by
        change ({w,x.val}:Finset V)={w,y.val} at h
        rw [←h]; simp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hs
      exact Subtype.ext (hs.resolve_left (adj x).ne')
    ⟩
  have h : (Finset.univ : Finset ↥S).map f = (G.cliqueFinset 2).filter (fun e => w∈e) := by
    ext e
    constructor
    · intro he
      obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr (pair_clique G (adj x)),by change w ∈ ({w,x.val}:Finset V); simp⟩
    · intro he
      obtain ⟨x,hx,h⟩ := pair_edge_at G w e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
      exact Finset.mem_map.mpr ⟨⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩,Finset.mem_univ _,h.symm⟩
  rw [←h,Finset.card_map,Finset.card_univ,Fintype.card_coe]

theorem handshake_clique_finset (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ w : V, (Upper.nbr G.Adj w).card) = 2*(G.cliqueFinset 2).card := by
  have eq (w : V) : (Upper.nbr G.Adj w).card =
      ∑ e ∈ G.cliqueFinset 2, if w∈e then (1:ℕ) else 0 := by
    rw [nbr_eq_incident_edges,←Finset.sum_filter,Finset.sum_const]
    simp
  simp only [eq]
  rw [Finset.sum_comm]
  have hh (e : Finset V) (he : e∈G.cliqueFinset 2) :
      (∑ w : V, if w∈e then (1:ℕ) else 0) = 2 := by
    rw [←Finset.sum_filter]
    simpa using (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  rw [show (∑ e ∈ G.cliqueFinset 2, ∑ w : V, if w∈e then (1:ℕ) else 0) =
    ∑ _e ∈ G.cliqueFinset 2, (2:ℕ) from Finset.sum_congr rfl hh]
  simp [Nat.mul_comm]

#print axioms handshake_clique_finset
end Erdős151.H12
