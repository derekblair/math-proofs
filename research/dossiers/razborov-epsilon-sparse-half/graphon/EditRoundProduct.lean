import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
open scoped BigOperators
namespace SparseHalfEditRound

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

noncomputable def prob (r : V → I → ℝ) (q : V → I) : ℝ := ∏ v, r v (q v)
noncomputable def expectation (r : V → I → ℝ) (f : (V → I) → ℝ) : ℝ :=
  ∑ q, prob r q * f q

theorem prob_nonneg (r : V → I → ℝ) (h : ∀ v i, 0 ≤ r v i) (q : V → I) :
    0 ≤ prob r q := Finset.prod_nonneg fun v _ => h v (q v)

theorem prob_total (r : V → I → ℝ) (h : ∀ v, ∑ i, r v i = 1) :
    ∑ q, prob r q = 1 := by
  classical
  unfold prob
  rw [← Fintype.prod_sum]
  simp [h]

theorem ex_mono (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (f g : (V → I) → ℝ) (h : ∀ q, f q ≤ g q) :
    expectation r f ≤ expectation r g := by
  unfold expectation
  exact Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (h q) (prob_nonneg r hr q)

theorem ex_add (r : V → I → ℝ) (f g : (V → I) → ℝ) :
    expectation r (fun q => f q + g q) = expectation r f + expectation r g := by
  simp [expectation,mul_add,Finset.sum_add_distrib]

theorem ex_mul (r : V → I → ℝ) (a : ℝ) (f : (V → I) → ℝ) :
    expectation r (fun q => a * f q) = a * expectation r f := by
  simp only [expectation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem ex_sum {J : Type*} (r : V → I → ℝ) (S : Finset J) (f : J → (V → I) → ℝ) :
    expectation r (fun q => ∑ j ∈ S, f j q) = ∑ j ∈ S, expectation r (f j) := by
  simp only [expectation,Finset.mul_sum]
  exact Finset.sum_comm

theorem exists_le_mean (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (hs : ∀ v, ∑ i, r v i = 1) (f : (V → I) → ℝ) :
    ∃ q, f q ≤ expectation r f := by
  classical
  have hn : ∃ q, 0 < prob r q := by
    by_contra! H
    have h := Finset.sum_nonpos (s := (Finset.univ : Finset (V → I))) (fun q _ => H q)
    rw [prob_total r hs] at h
    norm_num at h
  obtain ⟨q,hq⟩ := hn
  by_contra! H
  have hL (a : V → I) : prob r a * expectation r f ≤ prob r a * f a :=
    mul_le_mul_of_nonneg_left (H a).le (prob_nonneg r hr a)
  have hR : prob r q * expectation r f < prob r q * f q :=
    mul_lt_mul_of_pos_left (H q) hq
  have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset (V → I)))
    (fun a _ => hL a) ⟨q,Finset.mem_univ _,hR⟩
  rw [← Finset.sum_mul,prob_total r hs,one_mul] at hsum
  exact (lt_irrefl _ hsum)

private theorem ex_separable (r : V → I → ℝ) (s : V → I → ℝ) :
    expectation r (fun q => ∏ v, s v (q v)) =
      ∏ v, ∑ i, r v i * s v i := by
  classical
  simp only [expectation,prob,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun v i => r v i * s v i)).symm

theorem ex_one (r : V → I → ℝ) (hs : ∀ v, ∑ i, r v i = 1)
    (v : V) (f : I → ℝ) :
    expectation r (fun q => f (q v)) = ∑ i, r v i * f i := by
  classical
  let s (a : V) (i : I) : ℝ := if a=v then f i else 1
  have h (q : V → I) : (∏ a, s a (q a)) = f (q v) := by
    rw [Finset.prod_eq_single v]
    · simp [s]
    · intro a _ ha; simp [s,ha]
    · simp
  simp_rw [← h]
  rw [ex_separable,Finset.prod_eq_single v]
  · simp [s]
  · intro a _ ha; simp [s,ha,hs]
  · simp

theorem ex_two (r : V → I → ℝ) (hs : ∀ v, ∑ i, r v i = 1)
    (v w : V) (hv : v ≠ w) (f g : I → ℝ) :
    expectation r (fun q => f (q v)*g (q w)) = (∑ i, r v i*f i)*(∑ i,r w i*g i) := by
  classical
  let s (a : V) (i : I) : ℝ := if a=v then f i else if a=w then g i else 1
  have pl (F : V → ℝ) (H : ∀ a, a ≠ v → a ≠ w → F a = 1) :
      (∏ a, F a) = F v * F w := by
    have h := Finset.prod_erase_mul (s := (Finset.univ : Finset V)) (f := F) (Finset.mem_univ v)
    have hh : (∏ a ∈ (Finset.univ : Finset V).erase v, F a) = F w := by
      apply Finset.prod_eq_single w
      · intro a ha hw
        exact H a (Finset.mem_erase.mp ha).1 hw
      · intro hh
        exact False.elim (hh (Finset.mem_erase.mpr ⟨Ne.symm hv,Finset.mem_univ _⟩))
    rw [hh,mul_comm] at h
    exact h.symm
  have h (q : V → I) : (∏ a, s a (q a)) = f (q v)*g (q w) := by
    rw [pl _ (fun a ha hw => by simp [s,ha,hw])]
    simp [s,Ne.symm hv]
  simp_rw [← h]
  rw [ex_separable,pl _ (fun a ha hw => by simp [s,ha,hw,hs])]
  simp [s,Ne.symm hv]

#print axioms ex_two
#print axioms exists_le_mean
end SparseHalfEditRound
