import WagnerHostCut
import WagnerBypass
import WagnerFin8

namespace Erdős151.H12.Wagner
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]
  [DecidableEq V] [DecidableEq L] [DecidableEq R]

/-- A labeled Wagner link at each vertex of the host. Edges and triangles
are coded as distinct two- and three-element vertex sets, respectively. -/
structure HostWagnerLinks (E : L ↪ Finset V) (Tr : R ↪ Finset V) where
  slot : ∀ v : V, Fin 8 ≃ {x : V // x ≠ v ∧ hostRel E v x}
  adj : ∀ v i j, WagnerFin8.Adj i j →
    hostRel E ((slot v i).val) ((slot v j).val)
  triangle : ∀ v i j, WagnerFin8.Adj i j →
    ∃ t, Tr t = {v,(slot v i).val,(slot v j).val}

namespace HostWagnerLinks
set_option linter.unusedSectionVars false
variable {E : L ↪ Finset V} {Tr : R ↪ Finset V} (w : HostWagnerLinks E Tr)
include w

noncomputable def spoke (v : V) (i : Fin 8) : L :=
  Classical.choose (w.slot v i).property.2

theorem spoke_mem (v : V) (i : Fin 8) :
    v ∈ E (w.spoke v i) ∧ (w.slot v i).val ∈ E (w.spoke v i) :=
  Classical.choose_spec (w.slot v i).property.2

theorem spoke_set (e2 : ∀ e, (E e).card = 2) (v : V) (i : Fin 8) :
    E (w.spoke v i) = {v,(w.slot v i).val} := by
  have h := w.spoke_mem v i
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact h.1
    · exact h.2
  · rw [e2]
    simp [(w.slot v i).property.1.symm]

theorem spoke_of_contains (e2 : ∀ e, (E e).card = 2) (v : V) (e : L)
    (hv : v ∈ E e) : ∃ i, w.spoke v i = e := by
  have hnon : ∃ x ∈ E e, x ≠ v := by
    by_contra! h
    have hh : E e ⊆ {v} := by
      intro x hx
      exact Finset.mem_singleton.mpr (h x hx)
    have H := Finset.card_le_card hh
    simp [e2] at H
  obtain ⟨x,hx,hxv⟩ := hnon
  let a : {x : V // x ≠ v ∧ hostRel E v x} := ⟨x,hxv,e,hv,hx⟩
  let i := (w.slot v).symm a
  refine ⟨i,E.injective ?_⟩
  rw [w.spoke_set e2,show (w.slot v i).val=x from congrArg Subtype.val ((w.slot v).apply_symm_apply a)]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact hv
    · exact hx
  · rw [e2]
    simp [hxv.symm]

theorem local_split (e2 : ∀ e, (E e).card = 2) : localSplit E Tr := by
  classical
  intro S v h
  obtain ⟨e,he,f,hf,hve,hvf⟩ := h
  obtain ⟨i,hi⟩ := w.spoke_of_contains e2 v e hve
  obtain ⟨j,hj⟩ := w.spoke_of_contains e2 v f hvf
  let U := (Finset.univ : Finset (Fin 8)).filter (fun i => w.spoke v i ∈ S)
  have hiU : i ∈ U := by simp [U,hi,he]
  have hjU : j ∉ U := by simp [U,hj,hf]
  have hu0 : 0 < U.card := Finset.card_pos.mpr ⟨i,hiU⟩
  have hu8 : U.card < 8 := by
    have ss : U ⊂ (Finset.univ : Finset (Fin 8)) := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun e => hjU (e.symm ▸ Finset.mem_univ _)⟩
    simpa using Finset.card_lt_card ss
  let D := (U ×ˢ (Finset.univ \ U)).filter (fun a => WagnerFin8.Adj a.1 a.2)
  have Dsize : 3 ≤ D.card := WagnerFin8.edge_cut U hu0 hu8
  have exists_tri (a : ↥D) : ∃ t, Tr t =
      {v,(w.slot v a.val.1).val,(w.slot v a.val.2).val} :=
    w.triangle _ _ _ (Finset.mem_filter.mp a.property).2
  choose tr htr using exists_tri
  have inj : Function.Injective tr := by
    intro a b heq
    let x (i : Fin 8) := (w.slot v i).val
    have hset : ({v,x a.val.1,x a.val.2} : Finset V) =
        {v,x b.val.1,x b.val.2} := (htr a).symm.trans ((congrArg Tr heq).trans (htr b))
    have wx : Function.Injective x := fun i j h =>
      (w.slot v).injective (Subtype.ext h)
    have ha1 := (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1
    have ha2 := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).2).2
    have hb1 := (Finset.mem_product.mp (Finset.mem_filter.mp b.property).1).1
    have hb2 := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp b.property).1).2).2
    have H1 : x a.val.1 ∈ ({v,x b.val.1,x b.val.2} : Finset V) := by rw [← hset]; simp
    have H2 : x a.val.2 ∈ ({v,x b.val.1,x b.val.2} : Finset V) := by rw [← hset]; simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at H1 H2
    have p1 : a.val.1 = b.val.1 := by
      rcases H1 with h|h|h
      · exact False.elim ((w.slot v a.val.1).property.1 h)
      · exact wx h
      · exact False.elim (hb2 ((wx h) ▸ ha1))
    have p2 : a.val.2 = b.val.2 := by
      rcases H2 with h|h|h
      · exact False.elim ((w.slot v a.val.2).property.1 h)
      · exact False.elim (ha2 ((wx h).symm ▸ hb1))
      · exact wx h
    exact Subtype.ext (Prod.ext p1 p2)
  let J := (Finset.univ : Finset ↥D).map ⟨tr,inj⟩
  refine ⟨J,by simpa [J] using Dsize,?_⟩
  intro t ht
  obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp ht
  have ha1 := (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).1
  have ha2 := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp a.property).1).2).2
  refine ⟨w.spoke v a.val.1,(Finset.mem_filter.mp ha1).2,
    w.spoke v a.val.2,fun h => ha2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),
    (w.spoke_mem v a.val.1).1,(w.spoke_mem v a.val.2).1,?_,?_⟩
  
  · simp only [Function.Embedding.coeFn_mk]
    rw [w.spoke_set e2,htr]
    intro x h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
    exact h.elim Or.inl (fun h => Or.inr (Or.inl h))
  
  · simp only [Function.Embedding.coeFn_mk]
    rw [w.spoke_set e2,htr]
    intro x h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
    exact h.elim Or.inl (fun h => Or.inr (Or.inr h))

theorem local_bypass (v : V) (S : Finset V) (hS : S.card ≤ 2)
    (x y : V) (hx : hostRel E x v) (hy : hostRel E v y)
    (hxs : x ∉ S) (hys : y ∉ S) (hxv : x ≠ v) (hyv : y ≠ v) :
    Relation.ReflTransGen (WagnerBypass.restrict (hostRel E) (fun u => u ∉ S ∧ u ≠ v)) x y := by
  classical
  have hx' : hostRel E v x := by obtain ⟨a,h₁,h₂⟩ := hx; exact ⟨a,h₂,h₁⟩
  let i := (w.slot v).symm ⟨x,hxv,hx'⟩
  let j := (w.slot v).symm ⟨y,hyv,hy⟩
  let U := (Finset.univ : Finset (Fin 8)).filter (fun i => (w.slot v i).val ∈ S)
  have obs : U.card ≤ S.card := by
    let emb : Fin 8 ↪ V := ⟨fun i => (w.slot v i).val,fun i j h =>
      (w.slot v).injective (Subtype.ext h)⟩
    have hU : U.map emb ⊆ S := by
      intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
      exact (Finset.mem_filter.mp ha).2
    simpa using Finset.card_le_card hU
  have hi : (w.slot v i).val=x := congrArg Subtype.val ((w.slot v).apply_symm_apply _)
  have hj : (w.slot v j).val=y := congrArg Subtype.val ((w.slot v).apply_symm_apply _)
  have pl := WagnerFin8.connected_after_two U (obs.trans hS) i j
    (by simp [U,hi,hxs]) (by simp [U,hj,hys])
  have transfer {a b : Fin 8} (pp : Relation.ReflTransGen
      (fun l r => WagnerFin8.Adj l r ∧ l ∉ U ∧ r ∉ U) a b) :
      Relation.ReflTransGen (WagnerBypass.restrict (hostRel E) (fun u => u ∉ S ∧ u ≠ v))
        (w.slot v a).val (w.slot v b).val := by
    induction pp with
    | refl => exact .refl
    | tail _ step ih =>
      have left : _ := step.2.1
      have right : _ := step.2.2
      simp only [U,Finset.mem_filter,Finset.mem_univ,true_and] at left right
      exact .tail ih ⟨w.adj v _ _ step.1,⟨left,(w.slot v _).property.1⟩,
        ⟨right,(w.slot v _).property.1⟩⟩
  simpa only [hi,hj] using transfer pl

theorem global_avoid (conn : ∀ a b : V, Relation.ReflTransGen (hostRel E) a b)
    (U : Finset V) (hu : U.card ≤ 3) (a b : V) (ha : a ∉ U) (hb : b ∉ U) :
    Relation.ReflTransGen (fun x y => hostRel E x y ∧ x ∉ U ∧ y ∉ U) a b :=
  WagnerBypass.avoid_three (hostRel E) conn w.local_bypass U hu a b ha hb

theorem host_card_ge_eight (v : V) : 8 ≤ Fintype.card V := by
  have inj : Function.Injective (fun i : Fin 8 => (w.slot v i).val) :=
    fun i j h => (w.slot v).injective (Subtype.ext h)
  simpa using Fintype.card_le_of_injective _ inj

/-- Supply the entire graph-specific Hall cut interface from labeled Wagner links. -/
theorem small_cut (ec : ∀ e, (E e).card = 2) (tc : ∀ t, (Tr t).card = 3)
    (conn : ∀ a b : V, Relation.ReflTransGen (hostRel E) a b)
    (v : V) (P : Finset L) (hp : 4 ≤ P.card)
    (S : Finset L) (T : Finset R) (dS : Disjoint S P) (hs : 3 ≤ S.card)
    (hcut : cutMass (fun e t => E e ⊆ Tr t) S T ≤ 5) :
    mass (fun e t => E e ⊆ Tr t) S T < S.card + T.card :=
  small_host_cut E Tr ec tc ((by decide : (4:ℕ) ≤ 8).trans (w.host_card_ge_eight v))
    (w.local_split ec) (w.global_avoid conn) P hp S T dS hs hcut

end HostWagnerLinks
#print axioms HostWagnerLinks.local_split
#print axioms HostWagnerLinks.local_bypass
#print axioms HostWagnerLinks.small_cut
end Erdős151.H12.Wagner
