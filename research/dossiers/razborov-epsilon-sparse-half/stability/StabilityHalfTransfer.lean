import StabilityLift
open scoped BigOperators
namespace SparseHalfStability
variable {V T J : Type*} [Fintype V] [Fintype T] [DecidableEq T]

noncomputable def edgeCost {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
    (B : A → A → Bool) (s : A → ℝ) :=
  ∑ e ∈ Edges B, s e.1*s e.2

theorem canonical_cost {A : Type*} [Fintype A] [DecidableEq A] [LinearOrder A]
    (B : A → A → Bool) (s : A → ℝ) (sym : ∀ u v, B u v = B v u)
    (loop : ∀ u, B u u = false) :
    orderedCost B s = 2 * edgeCost B s := by
  classical
  let f (u v : A) : ℝ := if u < v ∧ B u v = true then s u*s v else 0
  have h (u v : A) : (if B u v then s u*s v else 0) = f u v + f v u := by
    rcases lt_trichotomy u v with H | rfl | H
    · cases h : B u v <;> simp [f,h,H,not_lt_of_gt H]
    · simp [loop,f]
    · cases h : B u v <;> simp [f,h,← sym u v,H,not_lt_of_gt H,mul_comm]
  have sums : (∑ u, ∑ v, f u v) = (∑ u, ∑ v, f v u) := Finset.sum_comm
  have HE : edgeCost B s = ∑ u, ∑ v, f u v := by
    unfold edgeCost Edges
    rw [Finset.sum_filter]
    change (∑ e : A × A, f e.1 e.2) = _
    rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [orderedCost,h,Finset.sum_add_distrib,← sums,HE]
  ring

variable [DecidableEq V] [LinearOrder V] [LinearOrder T] [Fintype J]

/-- Finite local theorem interface: given a repaired labeling and a
uniform sparse chart distribution for its class weights, obtain an
actual fractional sparse half. -/
theorem lift_and_transfer (B : T → T → Bool) (G : V → V → Bool) (q : V → T)
    (sv : ∀ u v, G u v = G v u) (st : ∀ a b, B a b = B b a)
    (lt : ∀ t, B t t = false)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (c eps : ℝ) (hc : 0 ≤ c) (ea : 2*(1+c)*eps ≤ c^2)
    (common_lower : ∀ e ∈ Edges G \ Edges (pull B q),
      c * Fintype.card V ≤ ((common (pull B q) e).card : ℝ))
    (cover_small : ∃ D : Finset V, Covers D (Edges G \ Edges (pull B q)) ∧
      (D.card : ℝ) ≤ eps * Fintype.card V)
    (degree : ∀ v : V,
      (((Edges G \ Edges (pull B q)).filter (OnEdge v)).card : ℝ) ≤ eps * Fintype.card V)
    (s : J → T → ℝ) (hj : Nonempty J)
    (ad : ∀ j t, 0 ≤ s j t ∧ s j t ≤ weight q t) (mass : ∀ j, ∑ t, s j t = 1/2)
    (cov : ∀ a b, B a b = true →
      (Fintype.card J : ℝ)*c*weight q a*weight q b ≤ ∑ j, s j a*s j b)
    (cost : (∑ j, edgeCost B (s j)) ≤ (Fintype.card J : ℝ)/50) :
    ∃ r : V → ℝ, (∀ v, 0 ≤ r v ∧ r v ≤ 1/(Fintype.card V : ℝ)) ∧
      (∑ v, r v) = 1/2 ∧ edgeCost G r ≤ 1/50 := by
  classical
  let r (j : J) := liftHalf q (s j)
  let f (e : V × V) : ℝ := ∑ j, r j e.1*r j e.2
  let n : ℝ := Fintype.card V
  let k : ℝ := Fintype.card J
  have lim (j : J) (v : V) := liftHalf_bounds q (s j) (ad j) v
  have up (e : V × V) (_ : e ∈ Edges G \ Edges (pull B q)) : f e ≤ k*(1/n)*(1/n) := by
    have H (j : J) : r j e.1*r j e.2 ≤ (1/n)*(1/n) :=
      mul_le_mul (lim j e.1).2 (lim j e.2).2 (lim j e.2).1
        ((lim j e.1).1.trans (lim j e.1).2)
    have Q := Finset.sum_le_sum (s := Finset.univ) (fun j _ => H j)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at Q
    simpa [f,k,mul_assoc] using Q
  have low (e : V × V) (he : e ∈ Edges (pull B q) \ Edges G) :
      c*(k*(1/n)*(1/n)) ≤ f e := by
    have he' : B (q e.1) (q e.2) = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2.2
    let A : ℝ := (fiber q (q e.1)).card
    let D : ℝ := (fiber q (q e.2)).card
    have hn (v : V) : 0 < ((fiber q (q v)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr
        (⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ : (fiber q (q v)).Nonempty)
    have hp : 0 < A*D := mul_pos (hn e.1) (hn e.2)
    have H (j : J) : r j e.1 * r j e.2 = (s j (q e.1)*s j (q e.2))/(A*D) := by
      simp [r,liftHalf,A,D,div_mul_div_comm]
    unfold f
    simp_rw [H,div_eq_mul_inv,← Finset.sum_mul]
    change _ ≤ ((∑ j, s j (q e.1)*s j (q e.2))/(A*D))
    rw [le_div_iff₀ hp]
    have Q := cov _ _ he'
    change k*c*(A/n)*(D/n) ≤ _ at Q
    calc
      _ = k*c*(A/n)*(D/n) := by ring
      _ ≤ _ := Q
  have cap : 0 ≤ k*(1/n)*(1/n) := by positivity
  have transfer := disturbed_cost (pull B q) G c eps (k*(1/n)*(1/n)) hc cap
    (fun _ _ => st _ _) sv tf common_lower cover_small degree ea f up low
  have eqCost (j : J) : edgeCost (pull B q) (r j) = edgeCost B (s j) := by
    have H := orderedCost_lift B q (s j) (ad j)
    change orderedCost (pull B q) (r j) = orderedCost B (s j) at H
    rw [canonical_cost (pull B q) (r j) (fun _ _ => st _ _) (fun _ => lt _),
      canonical_cost B (s j) st lt] at H
    linarith
  have swap (A : V → V → Bool) : ∑ e ∈ Edges A, f e = ∑ j, edgeCost A (r j) := by
    exact Finset.sum_comm
  rw [swap,swap] at transfer
  simp_rw [eqCost] at transfer
  have hex : ∃ j, edgeCost G (r j) ≤ 1/50 := by
    by_contra! H
    have hs := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset J))
      (Finset.univ_nonempty_iff.mpr hj) (fun j _ => H j)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    linarith
  obtain ⟨j,hj⟩ := hex
  exact ⟨r j,lim j,(liftHalf_mass q (s j) (ad j)).trans (mass j),hj⟩

#print axioms lift_and_transfer
end SparseHalfStability
