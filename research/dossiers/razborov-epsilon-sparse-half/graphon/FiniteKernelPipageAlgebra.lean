import FiniteKernelModel
open scoped BigOperators
namespace SparseHalfGraphon
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def form (A : V → V → ℝ) (x y : V → ℝ) : ℝ :=
  ∑ u, ∑ v, A u v*x u*y v

noncomputable def basis (x y : V) : ℝ := if y=x then 1 else 0
noncomputable def direction (i j : V) (v : V) : ℝ := basis i v-basis j v

theorem form_direction (A : V → V → ℝ)
    (sym : ∀ u v, A u v=A v u) (diag : ∀ v, A v v=0) (i j : V) :
    form A (direction i j) (direction i j) = -2*A i j := by
  unfold form direction
  have F (u : V) : (∑ v, A u v*(basis i u-basis j u)*(basis i v-basis j v)) =
      (A u i-A u j)*(basis i u-basis j u) := by
    have h (v : V) : A u v*(basis i u-basis j u)*(basis i v-basis j v) =
      (A u v*basis i v-A u v*basis j v)*(basis i u-basis j u) := by ring
    simp_rw [h]
    rw [← Finset.sum_mul,Finset.sum_sub_distrib]
    simp [basis,mul_ite]
  simp_rw [F]
  simp [mul_sub,basis,mul_ite,Finset.sum_sub_distrib,diag,sym j i]
  ring

theorem form_shift (A : V → V → ℝ) (x d : V → ℝ) (t : ℝ) :
    form A (fun v => x v+t*d v) (fun v => x v+t*d v) =
      form A x x+t*(form A d x+form A x d)+t^2*form A d d := by
  unfold form
  have h (u v : V) : A u v*(x u+t*d u)*(x v+t*d v) =
      A u v*x u*x v+t*(A u v*d u*x v)+t*(A u v*x u*d v)+t^2*(A u v*d u*d v) := by ring
  simp_rw [h,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem direction_self (i j : V) (h : i≠j) : direction i j i = 1 := by
  simp [direction,basis,h]

theorem direction_other (i j : V) (h : i≠j) : direction i j j = -1 := by
  simp [direction,basis,Ne.symm h]

theorem direction_zero (i j v : V) (hi : v≠i) (hj : v≠j) : direction i j v = 0 := by
  simp [direction,basis,hi,hj]

theorem direction_sum (i j : V) : ∑ v, direction i j v = 0 := by
  simp [direction,basis,Finset.sum_sub_distrib]

theorem favorable_shift (A : V → V → ℝ)
    (sym : ∀ u v, A u v=A v u) (diag : ∀ v, A v v=0)
    (nn : ∀ u v, 0≤A u v)
    (x : V → ℝ) (i j : V) (tp tn : ℝ) (hp : 0≤tp) (hn : 0≤tn) :
    (∃ t, (t=tp ∨ t= -tn) ∧
      form A (fun v => x v+t*direction i j v) (fun v => x v+t*direction i j v)
        ≤ form A x x) := by
  let L := form A (direction i j) x+form A x (direction i j)
  by_cases hL : L≤0
  · refine ⟨tp,Or.inl rfl,?_⟩
    rw [form_shift,form_direction A sym diag]
    have h := mul_nonpos_of_nonneg_of_nonpos hp hL
    have hh := mul_nonneg (sq_nonneg tp) (nn i j)
    linarith
  · refine ⟨-tn,Or.inr rfl,?_⟩
    rw [form_shift,form_direction A sym diag]
    have h := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hn) (le_of_not_ge hL)
    have hh := mul_nonneg (sq_nonneg (-tn)) (nn i j)
    linarith

#print axioms favorable_shift
end SparseHalfGraphon
