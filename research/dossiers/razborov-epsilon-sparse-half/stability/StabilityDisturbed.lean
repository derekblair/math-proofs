import StabilityCounting
import StabilityLoss
open scoped BigOperators
namespace SparseHalfStability

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

def Edges (B : V → V → Bool) : Finset (Edge (V := V)) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ B e.1 e.2 = true

private theorem undirected_missing (B G : V → V → Bool)
    (hB : ∀ u v, B u v = B v u) (hG : ∀ u v, G u v = G v u)
    (M : Finset (Edge (V := V))) :
    (crossMissing B G M).card ≤ (Edges B \ Edges G).card := by
  let f (e : Edge (V := V)) := if e.1 < e.2 then e else (e.2,e.1)
  have conditions (e : Edge (V := V)) (he : e ∈ crossMissing B G M) :
      e.1 ∈ Ends M ∧ e.2 ∉ Ends M ∧ B e.1 e.2 = true ∧ G e.1 e.2 = false :=
    (Finset.mem_filter.mp he).2
  apply Finset.card_le_card_of_injOn f
  · intro e he
    obtain ⟨hin,hout,hb,hg⟩ := conditions e he
    have hne : e.1 ≠ e.2 := fun hh => hout (hh ▸ hin)
    change f e ∈ Edges B \ Edges G
    unfold f
    split
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by assumption,hb⟩,
          fun hn => by simpa [hg] using (Finset.mem_filter.mp hn).2.2⟩
    · have hlt : e.2 < e.1 := lt_of_le_of_ne (le_of_not_gt (by assumption)) (Ne.symm hne)
      have hb' : B e.2 e.1 = true := (hB _ _).symm.trans hb
      have hg' : G e.2 e.1 = false := (hG _ _).symm.trans hg
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,hb'⟩,
          fun hn => by simpa [hg'] using (Finset.mem_filter.mp hn).2.2⟩
  · intro a ha b hb h
    have ha' := conditions a ha
    have hb' := conditions b hb
    unfold f at h
    split at h <;> split at h
    · exact h
    · have h' : a.1 = b.2 := congrArg Prod.fst h
      exact False.elim (hb'.2.1 (by rw [← h']; exact ha'.1))
    · have h' : a.2 = b.1 := congrArg Prod.fst h
      exact False.elim (ha'.2.1 (by rw [h']; exact hb'.1))
    · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

theorem disturbed_counts (B G : V → V → Bool) (c eps : ℝ)
    (hc : 0 ≤ c)
    (hB : ∀ u v, B u v = B v u) (hG : ∀ u v, G u v = G v u)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (common_lower : ∀ e ∈ Edges G \ Edges B,
      c * Fintype.card V ≤ ((common B e).card : ℝ))
    (cover_small : ∃ D : Finset V, Covers D (Edges G \ Edges B) ∧
      (D.card : ℝ) ≤ eps * Fintype.card V)
    (degree : ∀ v : V,
      (((Edges G \ Edges B).filter (OnEdge v)).card : ℝ) ≤ eps * Fintype.card V)
    (eps_bound : 2*(1+c)*eps ≤ c^2) :
    ((Edges G \ Edges B).card : ℝ) ≤ c * (Edges B \ Edges G).card := by
  let F := Edges G \ Edges B
  obtain ⟨D,hD,ds⟩ := cover_small
  obtain ⟨M,sub,mat,cov⟩ := exists_matching_cover F
  have hmd : (M.card : ℝ) ≤ D.card := by exact_mod_cast matching_le_cover F M D sub mat hD
  have hM := hmd.trans ds
  have plus (e : Edge (V := V)) (he : e ∈ M) : G e.1 e.2 = true :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (sub he)).1).2.2
  have hl := matching_lower B G M mat plus tf (fun e he => common_lower e (sub he))
  have hu := cover_degree_count F (Ends M) cov (fun v _ => degree v)
  have hends : ((Ends M).card : ℝ) ≤ 2*M.card := by exact_mod_cast card_ends M
  have hnon : 0 ≤ eps*(Fintype.card V : ℝ) := (Nat.cast_nonneg _).trans hM
  have hu' := hu.trans (mul_le_mul_of_nonneg_right hends hnon)
  have hmiss : ((crossMissing B G M).card : ℝ) ≤ (Edges B \ Edges G).card := by
    exact_mod_cast undirected_missing B G hB hG M
  apply edit_scalar c eps (Fintype.card V) M.card _ _ hc (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM eps_bound
  · nlinarith only [hu']
  · exact hl.trans hmiss

/-- Quantitative disturbed-subgraph transfer for edge expectations.
For a uniform sparse-half distribution, take f to be its expected edge product. -/
theorem disturbed_cost (B G : V → V → Bool) (c eps cap : ℝ)
    (hc : 0 ≤ c) (hcap : 0 ≤ cap)
    (hB : ∀ u v, B u v = B v u) (hG : ∀ u v, G u v = G v u)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (common_lower : ∀ e ∈ Edges G \ Edges B,
      c * Fintype.card V ≤ ((common B e).card : ℝ))
    (cover_small : ∃ D : Finset V, Covers D (Edges G \ Edges B) ∧
      (D.card : ℝ) ≤ eps * Fintype.card V)
    (degree : ∀ v : V,
      (((Edges G \ Edges B).filter (OnEdge v)).card : ℝ) ≤ eps * Fintype.card V)
    (eps_bound : 2*(1+c)*eps ≤ c^2)
    (f : Edge (V := V) → ℝ)
    (upper : ∀ e ∈ Edges G \ Edges B, f e ≤ cap)
    (lower : ∀ e ∈ Edges B \ Edges G, c*cap ≤ f e) :
    (∑ e ∈ Edges G, f e) ≤ ∑ e ∈ Edges B, f e :=
  cost_transfer (Edges B) (Edges G) f c cap hcap
    (disturbed_counts B G c eps hc hB hG tf common_lower cover_small degree eps_bound) upper lower

#print axioms disturbed_cost
end SparseHalfStability
