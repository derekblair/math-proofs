import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

namespace SparseDAG.SharedTight

variable {E R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
variable (w d : E → R)

theorem sum_le_of_pointwise (A : List E) (h : ∀ e ∈ A, d e ≤ w e) :
    (A.map d).sum ≤ (A.map w).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simpa only [List.map_cons, List.sum_cons] using
      add_le_add (h a (by simp)) (ih (fun e he => h e (by simp [he])))

theorem pointwise_of_sum_eq (A : List E) (h : ∀ e ∈ A, d e ≤ w e)
    (he : (A.map d).sum = (A.map w).sum) :
    ∀ e ∈ A, d e = w e := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have ha := h a (by simp)
    have hr (e : E) (m : e ∈ A) := h e (by simp [m])
    have H := sum_le_of_pointwise w d A hr
    simp only [List.map_cons, List.sum_cons] at he
    have ea : d a = w a := by
      apply le_antisymm ha
      by_contra! no
      exact (ne_of_lt (add_lt_add_of_lt_of_le no H)) he
    have rest : (A.map d).sum = (A.map w).sum := by
      rw [ea] at he
      exact add_left_cancel he
    intro e hm
    rcases List.mem_cons.mp hm with h0 | h1
    · rwa [h0]
    · exact ih hr rest e h1

theorem sum_eq_of_pointwise (A : List E) (h : ∀ e ∈ A, d e = w e) :
    (A.map d).sum = (A.map w).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons, h a (by simp),
      ih (fun e he => h e (by simp [he]))]

/-- For two paths between the same endpoints, each additive potential
telescopes to its own displacement independently of the path.
If each path is tight for its own feasible potential, both paths
are tight for both potentials. This also permits negative edge weights. -/
theorem exchange_tight (q : E → R) (A B : List E)
    (hA : ∀ e ∈ A, d e = w e) (hB : ∀ e ∈ B, q e = w e)
    (dFeasible : ∀ e ∈ B, d e ≤ w e)
    (qFeasible : ∀ e ∈ A, q e ≤ w e)
    (dTel : (A.map d).sum = (B.map d).sum)
    (qTel : (A.map q).sum = (B.map q).sum) :
    (∀ e ∈ A, q e = w e) ∧ (∀ e ∈ B, d e = w e) := by
  have hd := sum_eq_of_pointwise w d A hA
  have hq := sum_eq_of_pointwise w q B hB
  have dB := sum_le_of_pointwise w d B dFeasible
  have qA := sum_le_of_pointwise w q A qFeasible
  rw [←dTel, hd] at dB
  rw [qTel, hq] at qA
  have eq := le_antisymm dB qA
  exact ⟨pointwise_of_sum_eq w q A qFeasible (qTel.trans (hq.trans eq.symm)),
    pointwise_of_sum_eq w d B dFeasible (dTel.symm.trans (hd.trans eq))⟩
#print axioms exchange_tight

section Frobenius
variable {K : Type*} [CommSemiring K]
theorem sum_squares (S : List K) (h2 : (2:K)=0) :
    S.sum * S.sum = (S.map fun x => x*x).sum := by
  induction S with
  | nil => simp
  | cons x S ih =>
    simp only [List.sum_cons,List.map_cons]
    calc
      (x+S.sum)*(x+S.sum) = x*x + S.sum*S.sum + (2:K)*(x*S.sum) := by ring
      _ = x*x + (S.map fun x => x*x).sum := by rw [h2,zero_mul,add_zero,ih]

theorem product_squares (S : List K) :
    S.prod * S.prod = (S.map fun x => x*x).prod := by
  induction S with
  | nil => simp
  | cons x S ih =>
    simp only [List.prod_cons,List.map_cons]
    rw [← ih]
    ring
#print axioms sum_squares
#print axioms product_squares
end Frobenius
end SparseDAG.SharedTight
