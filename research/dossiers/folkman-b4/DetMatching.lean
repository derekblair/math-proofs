import DetSign
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace FolkmanB4.Critical
open Matrix Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def supported (I : V → V → Prop) (s : Equiv.Perm V) : Prop := ∀ i, I (s i) i
def weight {I : V → V → Prop} [DecidableRel I] (s : Equiv.Perm V) (e : ℚ) :
    Matrix V V ℚ := fun i j => if I i j then if i=s j then 1 else e else 0

theorem weight_positive (I : V → V → Prop) [DecidableRel I] (s : Equiv.Perm V) {e : ℚ}
    (he : 0<e) : PositivePattern I (weight (I:=I) s e) := by
  constructor
  · intro i j h
    simp only [weight,h,ite_true]
    split <;> positivity
  · intro i j h
    simp [weight,h]

def pSign (s : Equiv.Perm V) : ℚ := ((Equiv.Perm.sign s : ℤ) : ℚ)

theorem pSign_vals (s : Equiv.Perm V) : pSign s=1 ∨ pSign s=(-1) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · left; simp [pSign,h]
  · right; simp [pSign,h]

theorem weight_factor_bounds (I : V → V → Prop) [DecidableRel I] (s : Equiv.Perm V)
    {e : ℚ} (he : 0≤e) (eh : e≤1) (i j : V) :
    0≤weight (I:=I) s e i j ∧ weight (I:=I) s e i j ≤1 := by
  unfold weight
  split
  · split <;> simp [he,eh]
  · simp

theorem other_term_small (I : V → V → Prop) [DecidableRel I] (s t : Equiv.Perm V)
    {e : ℚ} (he : 0≤e) (eh : e≤1) (ne : t≠s) :
    |pSign t * ∏ i, weight (I:=I) s e (t i) i| ≤ e := by
  obtain ⟨i,h⟩ : ∃ i, t i≠s i := by
    by_contra not
    push Not at not
    exact ne (Equiv.ext not)
  let f (j : V) := weight (I:=I) s e (t j) j
  have fN (j : V) := (weight_factor_bounds I s he eh (t j) j).1
  have f1 (j : V) := (weight_factor_bounds I s he eh (t j) j).2
  have hi : f i≤e := by by_cases H : I (t i) i <;> simp [f,weight,H,h,he]
  have a : 0 ≤ ∏ j, f j := prod_nonneg fun j _ => fN j
  change |pSign t * ∏ j, f j| ≤ e
  rw [abs_mul,abs_of_nonneg a]
  have sg : |pSign t|=1 := (pSign_vals t).elim (fun h => by rw [h,abs_one])
    (fun h => by rw [h,abs_neg,abs_one])
  rw [sg,one_mul,←prod_erase_mul univ f (mem_univ i)]
  exact (mul_le_of_le_one_left (fN i) (prod_le_one₀ (fun j _ => fN j) (fun j _ => f1 j))).trans hi

theorem weight_det_close (I : V → V → Prop) [DecidableRel I] {s : Equiv.Perm V}
    (hs : supported I s) {e : ℚ} (he : 0≤e) (eh : e≤1) :
    |(weight (I:=I) s e).det-pSign s| ≤ (Fintype.card (Equiv.Perm V):ℚ)*e := by
  let F (t : Equiv.Perm V) := pSign t * ∏ i, weight (I:=I) s e (t i) i
  have ds : (weight (I:=I) s e).det=∑ t, F t := by rw [det_apply']; rfl
  have fs : F s=pSign s := by
    have p (i : V) : weight (I:=I) s e (s i) i=1 := by simp [weight,hs i]
    simp [F,p]
  rw [ds,←sum_erase_add univ F (mem_univ s),fs,add_sub_cancel_right]
  calc
    _ ≤ ∑ t ∈ (univ : Finset (Equiv.Perm V)).erase s, |F t| := abs_sum_le_sum_abs ..
    _ ≤ ∑ t ∈ (univ : Finset (Equiv.Perm V)).erase s, e := sum_le_sum fun t ht =>
      other_term_small I s t he eh (mem_erase.mp ht).1
    _ ≤ (Fintype.card (Equiv.Perm V):ℚ)*e := by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) he

theorem same_matching_sign (I : V → V → Prop) [DecidableRel I]
    (nonsing : ∀ A, PositivePattern I A → A.det≠0)
    {s t : Equiv.Perm V} (hs : supported I s) (ht : supported I t) :
    pSign s = pSign t := by
  let c : ℚ := Fintype.card (Equiv.Perm V)
  have hc : 0≤c := by positivity
  let e : ℚ := (c+1)⁻¹
  have ca : 0<c+1 := by linarith
  have he : 0<e := inv_pos.mpr ca
  have cb : e≤1 := (inv_le_one₀ ca).2 (by linarith)
  have eS := weight_det_close I hs he.le cb
  have eT := weight_det_close I ht he.le cb
  have bound : c*e<1 := by
    change c*(c+1)⁻¹<1
    rw [←div_eq_mul_inv,div_lt_iff₀ ca]
    linarith
  have sign := det_same_sign nonsing (weight_positive I s he) (weight_positive I t he)
  rcases pSign_vals s with hs' | hs' <;> rcases pSign_vals t with ht' | ht' <;>
    rw [hs',ht'] <;> try rfl
  · have S := abs_lt.mp (eS.trans_lt bound)
    have T := abs_lt.mp (eT.trans_lt bound)
    rw [hs'] at S
    rw [ht'] at T
    exact False.elim ((not_lt_of_ge (by linarith [T.2])) (sign.mp (by linarith [S.1])))
  · have S := abs_lt.mp (eS.trans_lt bound)
    have T := abs_lt.mp (eT.trans_lt bound)
    rw [hs'] at S
    rw [ht'] at T
    exact False.elim ((not_lt_of_ge (by linarith [S.2])) (sign.mpr (by linarith [T.1])))

#print axioms same_matching_sign
end FolkmanB4.Critical
