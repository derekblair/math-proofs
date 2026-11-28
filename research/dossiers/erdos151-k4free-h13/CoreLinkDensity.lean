import GraphDegreeTriangle

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

def linkSimple (G : SimpleGraph V) (w : V) : SimpleGraph V :=
  asSimple (fun a b => G.Adj a b ∧ G.Adj w a ∧ G.Adj w b)
    (fun h => ⟨h.1.symm,h.2.2,h.2.1⟩) (fun v h => (G.loopless.irrefl v) h.1)

instance linkDec (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    DecidableRel (linkSimple G w).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ G.Adj w a ∧ G.Adj w b))

theorem link_edges_eq_triangles (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    ((linkSimple G w).cliqueFinset 2).card =
      ((G.cliqueFinset 3).filter (fun t => w∈t)).card := by
  classical
  let J := linkSimple G w
  have pair_at (e : ↥(J.cliqueFinset 2)) :
      ∃ a b, e.val={a,b} ∧ G.Adj a b ∧ G.Adj w a ∧ G.Adj w b := by
    have h := SimpleGraph.mem_cliqueFinset_iff.mp e.property
    obtain ⟨a,b,ne,ht⟩ := Finset.card_eq_two.mp h.card_eq
    have ad := h.isClique (show a∈(e.val:Set V) by rw [ht]; simp)
      (show b∈(e.val:Set V) by rw [ht]; simp) ne
    exact ⟨a,b,ht,ad⟩
  have no_refl (e : ↥(J.cliqueFinset 2)) : w∉e.val := by
    obtain ⟨a,b,h,ab,wa,wb⟩ := pair_at e
    rw [h]
    intro hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl
    · exact (G.loopless.irrefl _) wa
    · exact (G.loopless.irrefl _) wb
  let m : ↥(J.cliqueFinset 2) ↪ Finset V := ⟨fun e => insert w e.val,by
    intro a b h
    change insert w a.val=insert w b.val at h
    have hh := congrArg (fun S : Finset V => S.erase w) h
    rw [Finset.erase_insert (no_refl a),Finset.erase_insert (no_refl b)] at hh
    exact Subtype.ext hh⟩
  have map : (Finset.univ : Finset ↥(J.cliqueFinset 2)).map m =
      (G.cliqueFinset 3).filter (fun t => w∈t) := by
    ext q
    constructor
    · intro h
      obtain ⟨e,_,rfl⟩ := Finset.mem_map.mp h
      obtain ⟨a,b,he,ab,wa,wb⟩ := pair_at e
      exact Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
        (show G.IsNClique 3 (insert w e.val) by
          rw [he]; exact SimpleGraph.is3Clique_triple_iff.mpr ⟨wa,wb,ab⟩),
        by change w∈insert w e.val; simp⟩
    · intro h
      obtain ⟨hc,hw⟩ := Finset.mem_filter.mp h
      let e := q.erase w
      have ej : e∈J.cliqueFinset 2 := by
        apply SimpleGraph.mem_cliqueFinset_iff.mpr
        have ht := SimpleGraph.mem_cliqueFinset_iff.mp hc
        refine ⟨?_,?_⟩
        · intro a ha b hb ne
          have ha' : a∈q.erase w := ha
          have hb' : b∈q.erase w := hb
          have hA := Finset.mem_erase.mp ha'
          have hB := Finset.mem_erase.mp hb'
          exact ⟨ht.isClique hA.2 hB.2 ne, ht.isClique hw hA.2 hA.1.symm,
            ht.isClique hw hB.2 hB.1.symm⟩
        · rw [Finset.card_erase_of_mem hw,ht.card_eq]
      exact Finset.mem_map.mpr ⟨⟨e,ej⟩,Finset.mem_univ _,Finset.insert_erase hw⟩
  rw [←map,Finset.card_map,Finset.card_univ,Fintype.card_coe]

theorem directed_link_sum (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    (∑ v ∈ Upper.nbr G.Adj w, ((Upper.nbr G.Adj w).filter (G.Adj v)).card) =
      2*((G.cliqueFinset 3).filter (fun t => w∈t)).card := by
  let J := linkSimple G w
  have hs (v : V) : Upper.nbr J.Adj v =
      if G.Adj w v then (Upper.nbr G.Adj w).filter (G.Adj v) else ∅ := by
    ext x
    by_cases h : G.Adj w v <;>
      simp [J,linkSimple,asSimple,Upper.nbr,h,and_comm]
  have hs' (v : V) : (Upper.nbr J.Adj v).card =
      if G.Adj w v then ((Upper.nbr G.Adj w).filter (G.Adj v)).card else 0 := by
    rw [hs]
    split <;> simp_all
  rw [← link_edges_eq_triangles G w,← handshake_clique_finset J]
  simp only [hs']
  rw [← Finset.sum_filter]
  rfl

#print axioms directed_link_sum
end Erdős151.H12
