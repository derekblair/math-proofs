import Core

namespace Wow268
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma adjacent_bound_tree {T : SimpleGraph V} [DecidableRel T.Adj] (hT : T.IsTree)
    {S : Finset V} (h : TotalDominating T S) :
    ∃ a b, T.Adj a b ∧ (∀ y, T.dist a y ≤ S.card) ∧ (∀ y, T.dist b y ≤ S.card) := by
  classical
  let U : Finset V := S ∪ Finset.univ.filter (fun v => 2 ≤ T.degree v)
  let H : SimpleGraph (↑U : Set V) := T.induce ↑U
  have hU {v : V} (hv : v ∈ S) : v ∈ U := Finset.mem_union_left _ hv
  have hn : Nonempty V := hT.connected.nonempty
  have hs := totalDominating_two_le h
  have hcard : U.card ≤ 2 * S.card - 2 := card_small_core hT h
  have hcard' : Fintype.card (↑U : Set V) = U.card := Fintype.card_coe U
  have hsmall : 1 < Fintype.card (↑U : Set V) := by
    rw [hcard']
    have hc := Finset.card_le_card (show S ⊆ U from fun _ hv => hU hv)
    omega
  haveI : Nontrivial (↑U : Set V) := Fintype.one_lt_card_iff_nontrivial.mp hsmall
  have hp : H.Preconnected := hT.connected.preconnected.induce_of_degree_eq_one (s := ↑U) (by
    intro v hv
    have hdeg : T.degree v ≤ 1 := by
      by_contra hh
      exact hv (Finset.mem_union_right _ (by simp; omega))
    have hsub : Subsingleton (T.neighborSet v) := Fintype.card_le_one_iff_subsingleton.mp (by
      rw [T.card_neighborSet_eq_degree]
      exact hdeg)
    intro x hx y hy
    exact congrArg Subtype.val (hsub.elim ⟨x,hx⟩ ⟨y,hy⟩))
  have ht : H.IsTree := ⟨⟨hp⟩, hT.isAcyclic.induce _⟩
  obtain ⟨x,z,hxz,hx,hz⟩ := adjacent_small_ecc_tree ht (k := S.card - 1) (by omega) (by omega)
  have liftBound (a : (↑U : Set V)) (ha : ∀ y, H.dist a y ≤ S.card - 1) (y : V) :
      T.dist a.val y ≤ S.card := by
    obtain ⟨u,hu,hyu⟩ := h y
    let u' : (↑U : Set V) := ⟨u,hU hu⟩
    obtain ⟨p,hpl⟩ := ht.connected.exists_walk_length_eq_dist a u'
    let p' := p.map (SimpleGraph.Embedding.induce (G := T) (↑U : Set V)).toHom
    have hp' : T.dist a.val u ≤ H.dist a u' := by
      have hh := SimpleGraph.dist_le p'
      change T.dist a.val u ≤
        (p.map (SimpleGraph.Embedding.induce (G := T) (↑U : Set V)).toHom).length at hh
      rwa [SimpleGraph.Walk.length_map, hpl] at hh
    have ht' := hT.connected.dist_triangle (u := a.val) (v := u) (w := y)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hyu.symm] at ht'
    have hab := ha u'
    omega
  exact ⟨x.val,z.val,hxz,liftBound x hx,liftBound z hz⟩

/-- Written on the Wall II, Conjecture 268 (November 5, 2026 catalogue).
    This is stated for every total dominating set, hence in particular a minimum one. -/
theorem graffiti268 (G : SimpleGraph V) (hc : G.Connected) (S : Finset V)
    (h : TotalDominating G S) : ⌊1 + avg G⌋ ≤ (S.card : ℤ) := by
  classical
  haveI := hc.nonempty
  obtain ⟨T,hTG,hT,hTd⟩ := spanning_keep_td hc h
  obtain ⟨a,b,hab,ha,hb⟩ := adjacent_bound_tree hT hTd
  have ea (x : V) (hx : ∀ y, T.dist x y ≤ S.card) : G.eccent x ≤ S.card := by
    apply iSup_le
    intro y
    calc
      G.edist x y ≤ T.edist x y := SimpleGraph.edist_anti hTG
      _ = ↑(T.dist x y) := (hT.connected x y |>.coe_dist_eq_edist).symm
      _ ≤ _ := by exact_mod_cast hx y
  have hrs := G.radius_le_eccent (u := a) |>.trans (ea a ha)
  apply conclude (totalDominating_two_le h) hrs
  intro heq
  have isCenter (x : V) (hx : ∀ y, T.dist x y ≤ S.card) : x ∈ G.center :=
    (G.mem_center_iff x).mpr (le_antisymm (heq ▸ ea x hx) G.radius_le_eccent)
  exact ⟨a,isCenter a ha,b,isCenter b hb,hTG hab⟩

/-- Connected graphs with at least two vertices have a total dominating set. -/
theorem td_exists (G : SimpleGraph V) [Nontrivial V] (hc : G.Connected) :
    ∃ n : ℕ, ∃ S : Finset V, S.card = n ∧ TotalDominating G S := by
  classical
  refine ⟨Fintype.card V,Finset.univ,by simp,?_⟩
  intro v
  obtain ⟨w,hw⟩ := exists_ne v
  obtain ⟨z,hvz,_⟩ := exists_first_side hc hw.symm
  exact ⟨z,Finset.mem_univ _,hvz⟩

/-- The minimum size of a total dominating set (for connected nontrivial graphs). -/
noncomputable def gammaT (G : SimpleGraph V) [Nontrivial V] (hc : G.Connected) : ℕ := by
  classical exact Nat.find (td_exists G hc)

/-- Exact numeric form of DeLaViña's WoWII conjecture 268. -/
theorem conjecture268 (G : SimpleGraph V) [Nontrivial V] (hc : G.Connected) :
    ⌊1 + avg G⌋ ≤ (gammaT G hc : ℤ) := by
  classical
  obtain ⟨S,hS,hTd⟩ := Nat.find_spec (td_exists G hc)
  have hNum : S.card = gammaT G hc := hS
  exact hNum ▸ graffiti268 G hc S hTd

#print axioms Wow268.graffiti268
#print axioms Wow268.conjecture268
end Wow268
