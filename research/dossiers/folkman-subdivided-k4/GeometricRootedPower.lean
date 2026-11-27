import GeometricRootedRates

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory

theorem rooted_power_errors (t X : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (Xp : 0<X) (hx : edgeRateClosed t+capRate t<X) :
    ∃ η B : ℝ, 0<η ∧ 1≤B ∧
    ∀ N : ℝ, B≤N → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E=graphDimension X N →
      let u := (patternMass (E:=E) triangleCon t).toReal
      let q := (patternMass (E:=E) diamondEdges t).toReal
      0<u ∧ 1/(N^2*u)≤N^(-η) ∧ q/(N*u^2)≤N^(-η) := by
  have ts' : t≤1/20000 := by linarith only [ts]
  obtain ⟨Ee,e⟩ := gram_max_exists edgeCon edgeCon_sym (by decide) t t0 ts'
  obtain ⟨Tr,tr⟩ := gram_max_exists triangleCon triangleCon_sym (by decide) t t0 ts'
  obtain ⟨Di,d⟩ := gram_max_exists diamondEdges diamond_sym (by decide) t t0 ts'
  obtain ⟨T2,D1⟩ := rooted_rate_room t X t0 ts' Ee Tr Di e tr d hx
  let a := -patternRate Tr/X
  let b := -patternRate Di/X
  have a2 : 0<2+a := by
    dsimp [a]
    rw [neg_div]
    linarith only [(div_lt_iff₀ Xp).2 T2]
  have bd : 0<1+2*a-b := by
    have q : (2*patternRate Tr-patternRate Di)/X<1 := (div_lt_iff₀ Xp).2 (by simpa using D1)
    simp only [sub_div,mul_div_assoc] at q
    dsimp [a,b]
    simp only [neg_div]
    linarith only [q]
  let s := min (2+a) (1+2*a-b)
  have sp : 0<s := lt_min a2 bd
  let δ := s/8
  let η := s/2
  have sl : s≤2+a := min_le_left _ _
  have sr : s≤1+2*a-b := min_le_right _ _
  obtain ⟨BT,bt,Tlaw⟩ := generic_power_rates triangleCon triangleCon_sym (by decide)
    t t0 ts Tr tr X δ Xp (by dsimp [δ]; positivity)
  obtain ⟨BD,bd,Dlaw⟩ := generic_power_rates diamondEdges diamond_sym (by decide)
    t t0 ts Di d X δ Xp (by dsimp [δ]; positivity)
  refine ⟨η,max BT BD,by dsimp [η]; positivity,bt.trans (le_max_left _ _),?_⟩
  intro N n E _ _ _ _ _ _ dim u q
  have N1 : 1≤N := bt.trans ((le_max_left _ _).trans n)
  have Np : 0<N := zero_lt_one.trans_le N1
  have T : N^(a-δ)≤u := (Tlaw N ((le_max_left _ _).trans n) E dim).1
  have D : q≤N^(b+δ) := (Dlaw N ((le_max_right _ _).trans n) E dim).2
  have u0 : 0<u := (Real.rpow_pos_of_pos Np _).trans_le T
  have loT : N^(2+(a-δ))≤N^2*u := by
    rw [Real.rpow_add Np,Real.rpow_two]
    exact mul_le_mul_of_nonneg_left T (by positivity)
  have loD : N^(1+2*(a-δ))≤N*u^2 := by
    rw [Real.rpow_add Np,Real.rpow_one,mul_comm (2:ℝ),Real.rpow_mul Np.le,Real.rpow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) T 2) Np.le
  have ratio (x y a b : ℝ) (hi : x≤N^a) (lo : N^b≤y) :
      x/y≤N^(a-b) := by
    have bp := Real.rpow_pos_of_pos Np b
    rw [Real.rpow_sub Np]
    exact (div_le_div_iff₀ (bp.trans_le lo) bp).2
      ((mul_le_mul_of_nonneg_right hi bp.le).trans (mul_le_mul_of_nonneg_left lo (by positivity)))
  refine ⟨u0,(ratio 1 _ 0 _ (by simp) loT).trans ?_,(ratio q _ _ _ D loD).trans ?_⟩
  all_goals apply Real.rpow_le_rpow_of_exponent_le N1
  · dsimp [δ,η]; linarith only [sl,sp]
  · dsimp [δ,η]; linarith only [sr,sp]

#print axioms rooted_power_errors
end RobustFolkman.GeometricGap
