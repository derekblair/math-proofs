import GeometricCapCoupling

namespace RobustFolkman.GeometricGap

theorem cap_gap_small_eventually (t : ℝ) (tp : 0<t) (ts : t≤1/40000) :
    ∃ n₀ : ℕ, ∀ n≥n₀, 3≤(n:ℝ)/2 ∧ 1≤4*((n:ℝ)/2)*t^2 ∧
      Real.sqrt (squaredCapContraction n t)≤1/200 := by
  obtain ⟨n₀,hn₀⟩ := exists_nat_ge (max (1000000:ℝ) (23/t^2))
  refine ⟨n₀,?_⟩
  intro n nn
  have nc : (n₀:ℝ)≤n := by exact_mod_cast nn
  have nL : (1000000:ℝ)≤n := (le_max_left _ _).trans (hn₀.trans nc)
  have nt : 23≤(n:ℝ)*t^2 :=
    (div_le_iff₀ (sq_pos_of_pos tp)).1 ((le_max_right _ _).trans (hn₀.trans nc))
  refine ⟨by linarith only [nL],by linarith only [nt],?_⟩
  apply (Real.sqrt_le_iff).2 ⟨by norm_num,?_⟩
  unfold squaredCapContraction
  have ee : Real.exp (3-2*((n:ℝ)/2)*t^2) ≤ (1/2:ℝ)^20 := by
    have e2 : (2:ℝ)≤Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    have high : (2:ℝ)^20≤Real.exp 20 := by
      have u := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) e2 20
      simpa only [←Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using u
    rw [div_pow,one_pow,one_div]
    calc
      _ ≤ Real.exp (-20) := Real.exp_le_exp.2 (by linarith only [nt])
      _ = (Real.exp 20)⁻¹ := Real.exp_neg _
      _ ≤ _ := inv_anti₀ (by positivity) high
  have inv : 1/((n:ℝ)+2)≤1/1000000 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [nL])
  have q := pow_le_pow_left₀ tp.le ts 2
  norm_num at ee q inv ⊢
  linarith only [ee,q,inv]

#print axioms cap_gap_small_eventually
end RobustFolkman.GeometricGap
