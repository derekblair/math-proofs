import GeometricDetLower

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def GramFeasible (C : I→I→Prop) (t : ℝ) (M : Matrix I I ℝ) : Prop :=
  M.PosSemidef ∧ (∀ i, M i i=1) ∧ ∀ i j, C i j → t≤M i j

noncomputable def smallProbe (C : I→I→Prop) [DecidableRel C] (t : ℝ) : Matrix I I ℝ :=
  fun i j => if i=j then 1 else if C i j then t else 0

theorem probe_exists (C : I→I→Prop) [DecidableRel C]
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000) :
    ∃ A : Matrix I I ℝ, GramFeasible C t A ∧ 1-719*t^2≤A.det := by
  let A := smallProbe C t
  have d : ∀ i, A i i=1 := fun i => by simp [A,smallProbe]
  have hsym : A.IsHermitian := by
    ext i j
    change star (A j i)=A i j
    rw [star_trivial]
    by_cases e : i=j
    · subst j
      rfl
    · by_cases e' : C i j
      · simp [A,smallProbe,e,Ne.symm e,e',(sym i j).mp e']
      · have n' : ¬C j i := fun h => e' ((sym i j).mpr h)
        simp [A,smallProbe,e,Ne.symm e,e',n']
  have off : ∀ i j, i≠j → |A i j|≤t := by
    intro i j ne
    by_cases e : C i j
    · simp [A,smallProbe,ne,e,abs_of_nonneg t0.le]
    · simp [A,smallProbe,ne,e,t0.le]
  have cn : (Fintype.card I : ℝ)≤6 := by exact_mod_cast n
  have rad : t*(Fintype.card I : ℝ)<1 := by
    have b := mul_le_mul_of_nonneg_left cn t0.le
    linarith only [b,ts]
  have pos : A.PosDef := by
    apply near_identity_pd A hsym t t0.le rad
    intro i j
    by_cases e : i=j
    · subst j
      simp [d,t0.le]
    · rw [Matrix.one_apply_ne e,sub_zero]
      exact off i j e
  refine ⟨A,⟨pos.posSemidef,d,?_⟩,determinant_six_lower A t t0.le (by linarith only [ts]) n d off⟩
  intro i j c
  by_cases e : i=j
  · subst j
    rw [d]
    linarith only [ts]
  · simp [A,smallProbe,e,c]

theorem optimum_is_localized (C : I→I→Prop) [DecidableRel C]
    (sym : ∀ i j, C i j ↔ C j i) (n : Fintype.card I≤6)
    (t : ℝ) (t0 : 0<t) (ts : t≤1/20000) (M : Matrix I I ℝ)
    (mf : GramFeasible C t M) (max : ∀ A, GramFeasible C t A → A.det≤M.det) :
    M.PosDef ∧ (∀ i j, |M i j-(1 : Matrix I I ℝ) i j|≤27*t) := by
  obtain ⟨A,af,ad⟩ := probe_exists C sym n t t0 ts
  have md := ad.trans (max A af)
  have hh : 0<1-719*t^2 := by
    have t2 : t^2≤(1/20000:ℝ)^2 := (sq_le_sq₀ t0.le (by norm_num)).mpr ts
    nlinarith only [t2]
  have dp := hh.trans_le md
  have md' : 1-729*t^2≤M.det := by nlinarith only [md,sq_nonneg t]
  exact ⟨pd_of_psd_det M mf.1 dp.ne',
    localized_offdiag M mf.1 dp.ne' mf.2.1 t t0.le md'⟩

#print axioms optimum_is_localized
end RobustFolkman.GeometricGap
