import StabilityEditTemplate
open scoped BigOperators
namespace SparseHalfStability
variable {V T : Type*} [Fintype V] [Fintype T] [DecidableEq T]

theorem sum_fibers (q : V → T) (f : V → ℝ) :
    (∑ t : T, ∑ v ∈ fiber q t, f v) = ∑ v, f v := by
  classical
  simp only [fiber,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq,eq_comm]

noncomputable def weight (q : V → T) (t : T) : ℝ :=
  (fiber q t).card / (Fintype.card V : ℝ)

noncomputable def liftHalf (q : V → T) (s : T → ℝ) (v : V) : ℝ :=
  s (q v) / (fiber q (q v)).card

theorem weight_mass (q : V → T) (h : 0 < Fintype.card V) : ∑ t, weight q t = 1 := by
  have P := sum_fibers q (fun _ => (1 : ℝ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ] at P
  simp only [weight,div_eq_mul_inv,← Finset.sum_mul,P]
  exact mul_inv_cancel₀ (by exact_mod_cast h.ne')

private theorem fiber_nonzero (q : V → T) (v : V) :
    0 < ((fiber q (q v)).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr
    (⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩ : (fiber q (q v)).Nonempty)

theorem liftHalf_bounds (q : V → T) (s : T → ℝ)
    (h : ∀ t, 0 ≤ s t ∧ s t ≤ weight q t) (v : V) :
    0 ≤ liftHalf q s v ∧ liftHalf q s v ≤ 1/(Fintype.card V : ℝ) := by
  have H := fiber_nonzero q v
  refine ⟨div_nonneg (h _).1 H.le, (div_le_iff₀ H).mpr ?_⟩
  unfold weight at h
  exact (h _).2.trans_eq (by ring)

theorem liftHalf_fiber (q : V → T) (s : T → ℝ)
    (h : ∀ t, 0 ≤ s t ∧ s t ≤ weight q t) (t : T) :
    ∑ v ∈ fiber q t, liftHalf q s v = s t := by
  classical
  have hc (v : V) (hv : v ∈ fiber q t) : liftHalf q s v = s t / (fiber q t).card := by
    unfold liftHalf
    rw [(Finset.mem_filter.mp hv).2]
  rw [Finset.sum_congr rfl hc]
  simp only [Finset.sum_const,nsmul_eq_mul]
  by_cases H : (fiber q t).card = 0
  · have H' : s t = 0 := by
      have := (h t).2
      unfold weight at this
      rw [H] at this
      simp at this
      exact le_antisymm this (h t).1
    simp [H,H']
  · have H' : ((fiber q t).card : ℝ) ≠ 0 := by exact_mod_cast H
    field_simp

theorem liftHalf_mass (q : V → T) (s : T → ℝ)
    (h : ∀ t, 0 ≤ s t ∧ s t ≤ weight q t) :
    ∑ v, liftHalf q s v = ∑ t, s t := by
  rw [← sum_fibers q (liftHalf q s)]
  exact Finset.sum_congr rfl fun t _ => liftHalf_fiber q s h t

noncomputable def orderedCost {A : Type*} [Fintype A] (B : A → A → Bool) (s : A → ℝ) :=
  ∑ u, ∑ v, if B u v then s u*s v else 0

theorem orderedCost_lift (B : T → T → Bool) (q : V → T) (s : T → ℝ)
    (h : ∀ t, 0 ≤ s t ∧ s t ≤ weight q t) :
    orderedCost (pull B q) (liftHalf q s) = orderedCost B s := by
  classical
  unfold orderedCost
  rw [← sum_fibers q]
  apply Finset.sum_congr rfl
  intro i _
  have hm (u : V) (hu : u ∈ fiber q i) :
      (∑ v, if pull B q u v then liftHalf q s u * liftHalf q s v else 0) =
        liftHalf q s u * (∑ j, if B i j then s j else 0) := by
    rw [← sum_fibers q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have H (v : V) (hv : v ∈ fiber q j) :
      (if pull B q u v then liftHalf q s u * liftHalf q s v else 0) =
        if B i j then liftHalf q s u * liftHalf q s v else 0 := by
      unfold pull
      rw [(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2]
    rw [Finset.sum_congr rfl H]
    cases hj : B i j <;> simp [hj, ← Finset.mul_sum, liftHalf_fiber q s h j]
  rw [Finset.sum_congr rfl hm, ← Finset.sum_mul, liftHalf_fiber q s h i, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by cases B i j <;> simp)

#print axioms liftHalf_mass
#print axioms orderedCost_lift
end SparseHalfStability
