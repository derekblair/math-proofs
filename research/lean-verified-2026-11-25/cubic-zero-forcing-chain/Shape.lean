import ForceUpper

namespace ZFChain
open Finset
set_option maxHeartbeats 1600000

def shortPath (m : Bool) (a : Fin 8) : Prop :=
  a = 6 ∨ localEdge m a 6 = true ∨
    (∃ b : Fin 8, localEdge m a b = true ∧ localEdge m b 6 = true) ∨
    (∃ b c : Fin 8, localEdge m a b = true ∧ localEdge m b c = true ∧ localEdge m c 6 = true)
instance (m) (a) : Decidable (shortPath m a) := by unfold shortPath; infer_instance

theorem local_shortPath (m : Bool) (a : Fin 8) (ha : legal m a) : shortPath m a := by
  cases m <;> fin_cases a <;> revert ha <;> decide

def hub {n} (i : Fin (n+2)) : V n := lift i 6 (Or.inr (by decide))

theorem from_edge {n} {x y : V n} (h : adj x y) : (chain n).Reachable x y :=
  ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil⟩

theorem local_reaches_hub {n} (x : V n) : (chain n).Reachable x (hub (blk x)) := by
  let i := blk x
  have H {u v : Fin 8} (hu : legal (mid i) u) (hv : legal (mid i) v)
      (h : localEdge (mid i) u v = true) :
      (chain n).Reachable (lift i u hu) (lift i v hv) :=
    from_edge (Or.inl ⟨rfl,h⟩)
  rw [← lift_eta x]
  change (chain n).Reachable (lift i (wire x) x.property) (hub i)
  rcases local_shortPath (mid i) _ x.property with hw | hw | ⟨b,hb,h6⟩ | ⟨b,c,hb,hc,h6⟩
  · change wire x = 6 at hw
    have he : lift i (wire x) x.property = hub i := vertex_ext rfl hw
    rw [he]
  · exact H _ _ hw
  · exact (H _ (locEdge_legal _ _ _ hb).2 hb).trans (H _ _ h6)
  · exact (H _ (locEdge_legal _ _ _ hb).2 hb).trans
      ((H _ (locEdge_legal _ _ _ hc).2 hc).trans (H _ _ h6))

theorem connectedChain (n : ℕ) : (chain n).Connected := by
  let origin : Fin (n+2) := ⟨0,by omega⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable (chain n)).mpr
  refine ⟨hub origin,?_⟩
  have all : ∀ (j : ℕ) (hj : j < n+2), (chain n).Reachable (hub origin) (hub ⟨j,hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact SimpleGraph.Reachable.rfl
    | succ j ih =>
      intro hj
      let e : Fin (n+1) := ⟨j,by omega⟩
      have hop : (chain n).Reachable (left e) (right e) :=
        from_edge (Or.inr ((cross_left _ _).mpr rfl))
      exact (ih (by omega)).trans ((local_reaches_hub (left e)).symm.trans hop)
  intro x
  exact (all (blk x).val (blk x).isLt).trans (local_reaches_hub x).symm

noncomputable section
open Classical
theorem cubicChain {n} (x : V n) :
    ((univ : Finset (V n)).filter (adj x)).card = 3 := by
  let L := (univ : Finset (V n)).filter (fun y => adj x y ∧ blk y = blk x)
  let R := (univ : Finset (V n)).filter (Cross x)
  have splitNbr : (univ : Finset (V n)).filter (adj x) = L ∪ R := by
    ext y
    simp only [L,R,mem_filter,mem_univ,true_and,mem_union]
    constructor
    · rintro (⟨h,q⟩|h)
      · exact Or.inl ⟨Or.inl ⟨h,q⟩,h.symm⟩
      · exact Or.inr h
    · rintro (⟨h,_⟩|h)
      · exact h
      · exact Or.inr h
  have hd : Disjoint L R := by
    apply disjoint_left.mpr
    intro u hu hv
    exact cross_ne (mem_filter.mp hv).2 (mem_filter.mp hu).2.2.symm
  have local_count : L.card = (locNbr (mid (blk x)) (wire x)).card := by
    have hh : L.image wire = locNbr (mid (blk x)) (wire x) := by
      ext a
      simp only [mem_image,locNbr,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨y,hy,rfl⟩
        have h := (mem_filter.mp hy).2
        exact (adj_same h.2.symm).mp h.1
      · intro e
        let y := lift (blk x) a (locEdge_legal _ _ _ e).2
        exact ⟨y,mem_filter.mpr ⟨mem_univ _, (adj_same (x := x) (y := y) rfl).mpr e,rfl⟩,rfl⟩
    rw [← hh,card_image_of_injOn]
    intro a ha b hb h
    exact vertex_ext ((mem_filter.mp ha).2.2.trans (mem_filter.mp hb).2.2.symm) h
  have hlc : (locNbr (mid (blk x)) (wire x)).card = if (wire x).val < 6 then 3 else 2 :=
    locNbr_classes (mid (blk x)) (wire x) x.property
  rw [splitNbr,card_union_of_disjoint hd,local_count,hlc]
  by_cases h : (wire x).val < 6
  · have hr : R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact core_not_cross h (mem_filter.mp hy).2
    simp [hr,h]
  · obtain ⟨y,hy,hu⟩ := cross_port_unique x (by omega)
    have hr : R = {y} := by
      ext z
      simp only [R,mem_filter,mem_univ,true_and,mem_singleton]
      exact ⟨hu z,fun h => h.symm ▸ hy⟩
    simp [hr,h]

theorem chain_degree {n} (x : V n) :
    haveI := Classical.decRel (chain n).Adj
    (chain n).degree x = 3 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  exact cubicChain x

end
end ZFChain
