import StabilityRepaired

open scoped BigOperators
namespace SparseHalfStability

variable {V I T : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  [Fintype I] [DecidableEq I] [DecidableEq T]

/-- Finite relabeling step used in local stability: the original labels
remain outside a small error set, each original fiber loses at most τ,
and extra edges have a small cover and small maximum degree.
The directed-error budget simplifies the counting by avoiding factors of two. -/
theorem edit_template (G : V → V → Bool) (B : T → T → Bool)
    (p : V → I) (embed : I → T)
    (symG : ∀ u v, G u v = G v u) (symB : ∀ a b, B a b = B b a)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (pat : ∀ s : Finset I, (∀ i ∈ s, ∀ j ∈ s, B (embed i) (embed j) = false) →
      ∃ a, ∀ i ∈ s, B a (embed i) = true)
    (codeg : ∀ a b, B a b = false → ∃ i, B a (embed i) = true ∧ B b (embed i) = true)
    (τ : ℝ) (hτ : 0 < τ)
    (budget : ((directedErrors G (fun i j => B (embed i) (embed j)) p).card : ℝ) ≤ τ^2)
    (large : ∀ i, 2*τ < ((fiber p i).card : ℝ)) :
    ∃ (q : V → T) (D : Finset V), ((D.card : ℝ) ≤ τ) ∧
      (∀ v ∉ D, q v = embed (p v)) ∧
      (∀ i, ((fiber p i).card : ℝ) ≤ (fiber q (embed i)).card + τ) ∧
      Covers D (Edges G \ Edges (pull B q)) ∧
      (∀ v, (((Edges G \ Edges (pull B q)).filter (OnEdge v)).card : ℝ) ≤
        (Fintype.card I+1)*τ) := by
  classical
  let H (i j : I) := B (embed i) (embed j)
  let D := bad G H p τ
  have hs : ((D.card : ℝ)) ≤ τ := bad_size G H p τ hτ budget
  have hp (v : V) : ∃ a, ∀ i ∈ heavy G p τ v, B a (embed i) = true :=
    pat (heavy G p τ v) (fun i hi j hj => heavy_independent G H p tf τ hτ.le budget v i j hi hj)
  let q (v : V) := if v ∈ D then Classical.choose (hp v) else embed (p v)
  have go (v : V) (hv : v ∉ D) : q v = embed (p v) := by simp [q,hv]
  have ad (v : V) (hv : v ∈ D) : ∀ i ∈ heavy G p τ v, B (q v) (embed i) = true := by
    simpa [q,hv] using Classical.choose_spec (hp v)
  have low (v : V) (hv : v ∉ D) : ((err G H p v).card : ℝ) ≤ τ := by
    apply le_of_not_gt
    intro h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have noextras (v u : V) (hv : v ∉ D) (hu : u ∉ D)
      (hB : pull B q v u = false) : G v u = false := by
    have hb : B (embed (p v)) (embed (p u)) = false := by
      simpa only [pull,go v hv,go u hu] using hB
    obtain ⟨i,hi,hj⟩ := codeg _ _ hb
    exact good_pair G H p tf τ v u i hi hj (low v hv) (low u hu) (large i)
  have cv : Covers D (Edges G \ Edges (pull B q)) := by
    intro e he
    by_contra! hen
    obtain ⟨H1,H2⟩ := Finset.mem_sdiff.mp he
    obtain ⟨hlt,hg⟩ := (Finset.mem_filter.mp H1).2
    have hb : pull B q e.1 e.2 = false := by
      by_contra hh
      exact H2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,by simpa using hh⟩)
    exact Bool.noConfusion ((noextras e.1 e.2 hen.1 hen.2 hb).symm.trans hg)
  refine ⟨q,D,hs,go,fun i => (repaired_fiber p q embed D go i).trans (by linarith),
    cv,?_⟩
  intro v
  refine (edge_degree (pull B q) G (fun u v => symB _ _) symG v).trans ?_
  change ((extras G B q v).card : ℝ) ≤ _
  have hout : ((extras G B q v \ D).card : ℝ) ≤ (Fintype.card I : ℝ)*τ := by
    by_cases hv : v ∈ D
    · exact exterior_count G B p q embed D go τ hτ.le ad v hv
    · have h0 : extras G B q v \ D = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨hu1,hu2⟩ := Finset.mem_sdiff.mp hu
        obtain ⟨hg,hb⟩ := (Finset.mem_filter.mp hu1).2
        exact Bool.noConfusion ((noextras v u hv hu2 hb).symm.trans hg)
      simpa [h0] using mul_nonneg (Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ _) hτ.le
  have hg : ((extras G B q v).card : ℝ) ≤ (extras G B q v \ D).card + D.card := by
    exact_mod_cast ((Finset.card_sdiff_add_card_inter (extras G B q v) D).symm.trans_le
      (Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _))
  linarith

#print axioms edit_template
end SparseHalfStability
