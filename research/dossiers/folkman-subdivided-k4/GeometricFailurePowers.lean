import GeometricPowerRates

namespace RobustFolkman.GeometricGap

private theorem rpow_div_upper (N a b : ℝ) (hN : 1≤N)
    (x y : ℝ) (x' : x≤N^a) (y' : N^b≤y) :
    x/y ≤ N^(a-b) := by
  have Np := zero_lt_one.trans_le hN
  have b0 := Real.rpow_pos_of_pos Np b
  have y0 := b0.trans_le y'
  rw [Real.rpow_sub Np]
  exact (div_le_div_iff₀ y0 b0).mpr
    ((mul_le_mul_of_nonneg_right x' b0.le).trans (mul_le_mul_of_nonneg_left y'
      (Real.rpow_pos_of_pos Np a).le))

private theorem rpow_prod_sq (N u e : ℝ) (Np : 0<N) (u0 : 0≤u)
    (lo : N^e≤u) :
    N^(2+2*e)≤N^2*u^2 := by
  rw [Real.rpow_add Np, Real.rpow_two, mul_comm (2:ℝ) e,
    Real.rpow_mul Np.le,Real.rpow_two]
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.rpow_pos_of_pos Np _).le u0).mpr lo) (sq_nonneg _)

theorem four_failure_power_bounds (N a b c d δ η u v h j : ℝ) (N1 : 1≤N)
    (uLo : N^(a-δ)≤u) (vHi : v≤N^(b+δ)) (hHi : h≤N^(c+δ)) (jHi : j≤N^(d+δ))
    (brT : -(3+a-δ)≤ -η) (brD : b+3*δ-2-2*a≤ -η)
    (brH : 2+c+2*δ-a≤ -η) (brJ : 3+d+2*δ-a≤ -η) :
    1/(N^3*u)≤N^(-η) ∧ v/(N^2*u^2)≤N^(-η) ∧
      N^2*h/u≤N^(-η) ∧ N^3*j/u≤N^(-η) := by
  have Np := zero_lt_one.trans_le N1
  have u0 := (Real.rpow_pos_of_pos Np (a-δ)).trans_le uLo
  have one : 1≤N^(0:ℝ) := by simp
  have tLo : N^(3+(a-δ))≤N^3*u := by
    rw [Real.rpow_add Np, ← Real.rpow_natCast N 3]
    exact mul_le_mul_of_nonneg_left uLo (by positivity)
  have dLo := rpow_prod_sq N u (a-δ) Np u0.le uLo
  have hp : N^2*h≤N^(2+(c+δ)) := by
    rw [Real.rpow_add Np, Real.rpow_two]
    exact mul_le_mul_of_nonneg_left hHi (by positivity)
  have jp : N^3*j≤N^(3+(d+δ)) := by
    rw [Real.rpow_add Np, ← Real.rpow_natCast N 3]
    exact mul_le_mul_of_nonneg_left jHi (by positivity)
  refine ⟨(rpow_div_upper N _ _ N1 1 _ one tLo).trans ?_,
    (rpow_div_upper N _ _ N1 v _ vHi dLo).trans ?_,
    (rpow_div_upper N _ _ N1 (N^2*h) _ hp uLo).trans ?_,
    (rpow_div_upper N _ _ N1 (N^3*j) _ jp uLo).trans ?_⟩
  all_goals apply Real.rpow_le_rpow_of_exponent_le N1
  · linarith only [brT]
  · linarith only [brD]
  · linarith only [brH]
  · linarith only [brJ]

theorem failure_exponent_room (X T D H J : ℝ) (Xp : 0<X)
    (T3 : T<3*X) (D2 : 2*T-D<2*X) (H2 : 2*X<H-T) (J3 : 3*X<J-T) :
    ∃ δ η : ℝ, 0<δ ∧ 0<η ∧
      -(3+(-T/X)-δ) ≤ -η ∧
      (-D/X)+3*δ-2-2*(-T/X) ≤ -η ∧
      2+(-H/X)+2*δ-(-T/X) ≤ -η ∧
      3+(-J/X)+2*δ-(-T/X) ≤ -η := by
  let a := 3-T/X
  let b := 2-(2*T-D)/X
  let c := (H-T)/X-2
  let d := (J-T)/X-3
  have ap : 0<a := sub_pos.mpr ((div_lt_iff₀ Xp).mpr T3)
  have bp : 0<b := sub_pos.mpr ((div_lt_iff₀ Xp).mpr D2)
  have cp : 0<c := sub_pos.mpr ((lt_div_iff₀ Xp).mpr H2)
  have dp : 0<d := sub_pos.mpr ((lt_div_iff₀ Xp).mpr J3)
  let s := min (min a b) (min c d)
  have sp : 0<s := lt_min (lt_min ap bp) (lt_min cp dp)
  have sa : s≤a := (min_le_left _ _).trans (min_le_left _ _)
  have sb : s≤b := (min_le_left _ _).trans (min_le_right _ _)
  have sc : s≤c := (min_le_right _ _).trans (min_le_left _ _)
  have sd : s≤d := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s/8,s/2,by positivity,by positivity, ?_,?_,?_,?_⟩
  all_goals dsimp [a,b,c,d] at sa sb sc sd
  · rw [neg_div]
    linarith only [sa,sp]
  · simp only [neg_div,sub_div] at *
    rw [mul_div_assoc] at sb
    linarith only [sb,sp]
  · simp only [neg_div,sub_div] at *
    linarith only [sc,sp]
  · simp only [neg_div,sub_div] at *
    linarith only [sd,sp]

#print axioms four_failure_power_bounds
#print axioms failure_exponent_room
end RobustFolkman.GeometricGap
