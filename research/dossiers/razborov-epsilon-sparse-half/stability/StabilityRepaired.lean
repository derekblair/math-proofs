import StabilityRelabel

open scoped BigOperators
namespace SparseHalfStability

variable {V I T : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  [Fintype I] [DecidableEq I] [DecidableEq T]

def pull (B : T → T → Bool) (q : V → T) (v w : V) := B (q v) (q w)

theorem repaired_fiber (p : V → I) (q : V → T) (embed : I → T) (D : Finset V)
    (go : ∀ v ∉ D, q v = embed (p v)) (i : I) :
    ((fiber p i).card : ℝ) ≤ (fiber q (embed i)).card + D.card := by
  have hs : fiber p i ⊆ fiber q (embed i) ∪ D := by
    intro x hx
    by_cases H : x ∈ D
    · exact Finset.mem_union.mpr (Or.inr H)
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [go x H,(Finset.mem_filter.mp hx).2]⟩
  exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem repaired_common (B : T → T → Bool) (q : V → T) (embed : I → T)
    (codeg : ∀ a b, B a b = false → ∃ i, B a (embed i) = true ∧ B b (embed i) = true)
    (fiberSize : ∀ i, K ≤ ((fiber q (embed i)).card : ℝ))
    (e : Edge (V := V)) (he : pull B q e.1 e.2 = false) :
    K ≤ ((common (pull B q) e).card : ℝ) := by
  obtain ⟨i,hi,hj⟩ := codeg (q e.1) (q e.2) he
  have hsub : fiber q (embed i) ⊆ common (pull B q) e := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    dsimp [pull]
    rw [(Finset.mem_filter.mp hv).2]
    exact ⟨hi,hj⟩
  exact (fiberSize i).trans (by exact_mod_cast Finset.card_le_card hsub)

theorem edge_degree (B G : V → V → Bool) (symB : ∀ u v, B u v = B v u)
    (symG : ∀ u v, G u v = G v u) (v : V) :
    (((Edges G \ Edges B).filter (OnEdge v)).card : ℝ) ≤
      ((Finset.univ.filter (fun x => G v x = true ∧ B v x = false)).card : ℝ) := by
  let f (e : Edge (V := V)) := if e.1 = v then e.2 else e.1
  have all (e : Edge (V := V)) (he : e ∈ (Edges G \ Edges B).filter (OnEdge v)) :
      (e.1 < e.2 ∧ G e.1 e.2 = true ∧ B e.1 e.2 = false) ∧ OnEdge v e := by
    obtain ⟨hd,hon⟩ := Finset.mem_filter.mp he
    obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hlt,ha⟩ := (Finset.mem_filter.mp hg).2
    have hb : B e.1 e.2 = false := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,by simpa using hh⟩)
    exact ⟨⟨hlt,ha,hb⟩,hon⟩
  have h := Finset.card_le_card_of_injOn (s := ((Edges G \ Edges B).filter (OnEdge v)))
      (t := Finset.univ.filter (fun x => G v x = true ∧ B v x = false)) f (by
    intro e he
    obtain ⟨⟨hlt,hg,hb⟩,hv⟩ := all e he
    change f e ∈ Finset.univ.filter _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    unfold f
    split
    · simpa only [← ‹e.1 = v›] using And.intro hg hb
    · have eq : v = e.2 := hv.resolve_left (Ne.symm (by assumption))
      rw [eq, ← symG e.1 e.2, ← symB e.1 e.2]
      exact ⟨hg,hb⟩) (by
    intro a ha b hb h
    have A := (all a ha).1.1
    have B' := (all b hb).1.1
    have Av := (all a ha).2
    have Bv := (all b hb).2
    unfold f at h
    split at h <;> split at h
    · exact Prod.ext ((show a.1 = v by assumption).trans (show b.1 = v by assumption).symm) h
    · have be : v = b.2 := Bv.resolve_left (Ne.symm (by assumption))
      have av : a.1 = v := by assumption
      exact False.elim ((lt_asymm A) (by rw [h,av,be]; exact B'))
    · have ae : v = a.2 := Av.resolve_left (Ne.symm (by assumption))
      have bv : b.1 = v := by assumption
      exact False.elim ((lt_asymm B') (by rw [← h,bv,ae]; exact A))
    · exact Prod.ext h
        ((Av.resolve_left (Ne.symm (by assumption))).symm.trans
          (Bv.resolve_left (Ne.symm (by assumption)))))
  exact_mod_cast h

#print axioms repaired_common
#print axioms edge_degree
end SparseHalfStability
