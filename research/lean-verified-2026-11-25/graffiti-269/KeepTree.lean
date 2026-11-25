import Wow268
import Adjacent

open scoped Sym2
namespace Wow268
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma preserve_delete {S : Finset V} (h : TotalDominating G S) {a b : V}
    (ha : ∃ u ∈ S, G.Adj a u ∧ u ≠ b)
    (hb : ∃ u ∈ S, G.Adj b u ∧ u ≠ a) :
    TotalDominating (G.deleteEdges {s(a,b)}) S := by
  intro v
  by_cases hva : v = a
  · subst v
    obtain ⟨u, hu, huu, hne⟩ := ha
    refine ⟨u, hu, SimpleGraph.deleteEdges_adj.mpr ⟨huu, ?_⟩⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    exact fun he => he.elim (fun he => hne he.2) (fun he => huu.ne he.2.symm)
  by_cases hvb : v = b
  · subst v
    obtain ⟨u, hu, huu, hne⟩ := hb
    refine ⟨u, hu, SimpleGraph.deleteEdges_adj.mpr ⟨huu, ?_⟩⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    exact fun he => he.elim (fun he => hva he.1) (fun he => hne he.2)
  obtain ⟨u, hu, huv⟩ := h v
  refine ⟨u, hu, SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩⟩
  simp only [Set.mem_singleton_iff, Sym2.eq_iff]
  exact fun he => he.elim (fun he => hva he.1) (fun he => hvb he.1)

lemma two_cycle_neighbors {v x : V} {p : G.Walk v v} (hp : p.IsCycle)
    (hx : x ∈ p.support) :
    ∃ y z, G.Adj x y ∧ G.Adj x z ∧ y ≠ z ∧ y ∈ p.support ∧ z ∈ p.support ∧
      s(x,y) ∈ p.edges ∧ s(x,z) ∈ p.edges := by
  let q := p.rotate x hx
  have hq := hp.rotate hx
  have hq' : q.IsCycle := hq
  have hs (w : V) : w ∈ q.support ↔ w ∈ p.support := p.mem_support_rotate_iff x hx
  have he (e : Sym2 V) : e ∈ q.edges ↔ e ∈ p.edges := (p.rotate_edges x hx).perm.mem_iff
  exact ⟨q.snd, q.penultimate, q.adj_snd hq'.not_nil, (q.adj_penultimate hq'.not_nil).symm,
    hq'.snd_ne_penultimate, (hs _).1 (List.mem_of_mem_tail (q.snd_mem_tail_support hq'.not_nil)),
    (hs _).1 (List.mem_of_mem_dropLast (q.penultimate_mem_dropLast_support hq'.not_nil)),
    (he _).1 (q.mk_start_snd_mem_edges hq'.not_nil),
    (he _).1 (Sym2.eq_swap ▸ q.mk_penultimate_end_mem_edges hq'.not_nil)⟩

lemma cycle_removable {S : Finset V} (h : TotalDominating G S)
    {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    ∃ e ∈ p.edges, TotalDominating (G.deleteEdges {e}) S := by
  by_cases hin : ∀ x ∈ p.support, x ∈ S
  · have hv : v ∈ p.support := p.start_mem_support
    obtain ⟨y,z,hvy,hvz,hyz,hy,hz,hey,_⟩ := two_cycle_neighbors hp hv
    obtain ⟨a,b,hya,hyb,hab,ha,hb,_,_⟩ := two_cycle_neighbors hp hy
    refine ⟨s(v,y), hey, preserve_delete h ⟨z, hin z hz, hvz, hyz.symm⟩ ?_⟩
    by_cases h : a = v
    · exact ⟨b, hin b hb, hyb, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨a, hin a ha, hya, h⟩
  · push Not at hin
    obtain ⟨x,hx,hxs⟩ := hin
    obtain ⟨a,b,hxa,hxb,hab,_,_,hea,heb⟩ := two_cycle_neighbors hp hx
    obtain ⟨t,ht,hxt⟩ := h x
    by_cases hta : t = a
    · obtain ⟨u,hu,hbu⟩ := h b
      exact ⟨s(x,b), heb, preserve_delete h ⟨t,ht,hxt,hta.trans_ne hab⟩
        ⟨u,hu,hbu,fun he => hxs (he ▸ hu)⟩⟩
    · obtain ⟨u,hu,hau⟩ := h a
      exact ⟨s(x,a), hea, preserve_delete h ⟨t,ht,hxt,hta⟩
        ⟨u,hu,hau,fun he => hxs (he ▸ hu)⟩⟩

lemma spanning_keep_td (hc : G.Connected) {S : Finset V} (h : TotalDominating G S) :
    ∃ T ≤ G, T.IsTree ∧ TotalDominating T S := by
  classical
  let P := {H : SimpleGraph V | H ≤ G ∧ H.Connected ∧ TotalDominating H S}
  obtain ⟨T,hT,hmin⟩ := Set.exists_min_image P
    (fun H => Nat.card H.edgeSet) (Set.toFinite P) ⟨G,le_rfl,hc,h⟩
  obtain ⟨hTG,hTc,hTd⟩ := hT
  refine ⟨T,hTG,⟨hTc,?_⟩,hTd⟩
  intro v p hp
  obtain ⟨e,he,hEd⟩ := cycle_removable hTd hp
  have he' := p.edges_subset_edgeSet he
  have hnb : ¬ T.IsBridge e := fun h => h.notMem_edges_of_isCycle hp he
  let U := T.deleteEdges {e}
  have hUT : U ≤ T := T.deleteEdges_le _
  have hUc : U.Connected := hTc.preconnected.connected_deleteEdges_of_not_isBridge hnb
  have hlt : U < T := by
    refine lt_of_le_of_ne hUT (fun hEq => ?_)
    have hmem : e ∈ U.edgeSet := hEq.symm ▸ he'
    simpa [U,SimpleGraph.edgeSet_deleteEdges] using hmem
  have hcard : Nat.card U.edgeSet < Nat.card T.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← U.edgeFinset_card, ← T.edgeFinset_card]
    exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
  exact (not_lt_of_ge (hmin U ⟨hUT.trans hTG,hUc,hEd⟩)) hcard

end Wow268
