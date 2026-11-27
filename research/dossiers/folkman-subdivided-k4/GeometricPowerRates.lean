import GeometricDimensionScaling

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem sphere_pattern_power_rates (C : Fin n→Fin n→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (small : n≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (M : Matrix (Fin n) (Fin n) ℝ) (mf : GramFeasible C t M)
    (opt : ∀ A, GramFeasible C t A → A.det≤M.det) (X δ : ℝ) (Xp : 0<X) (dp : 0<δ) :
    ∃ N0 : ℝ, 1≤N0 ∧ ∀ N : ℝ, N0≤N →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E=graphDimension X N →
      N^(Real.log M.det/(2*X)-δ) ≤ (spherePatternMass (E:=E) C t).toReal ∧
      (spherePatternMass (E:=E) C t).toReal ≤ N^(Real.log M.det/(2*X)+δ) := by
  let ε := δ*X/3
  have ep : 0<ε := by dsimp [ε]; positivity
  let R := Real.log M.det/2
  obtain ⟨cut,cp,law⟩ := sphere_pattern_rate C sym small t t0 ts M mf opt ε ep
  let A : ℝ := (n:ℝ)+1
  let K := max (A + 2*cut) (A*(|R|+ε)/ε)
  have Ka : A+2*cut≤K := le_max_left _ _
  have Kr : A*(|R|+ε)/ε≤K := le_max_right _ _
  have Kp : 0<K := (by dsimp [A]; positivity : 0<A+2*cut).trans_le Ka
  let N0 := Real.exp (X*K)
  have N01 : 1≤N0 := Real.one_le_exp (mul_nonneg Xp.le Kp.le)
  refine ⟨N0,N01,?_⟩
  intro N large E _ _ _ _ _ _ dim
  have oneN : 1≤N := N01.trans large
  have posN : 0<N := zero_lt_one.trans_le oneN
  have logs := (Real.log_le_log_iff (Real.exp_pos (X*K)) posN).mpr large
  rw [Real.log_exp] at logs
  have LK : K≤Real.log N/X := (le_div_iff₀ Xp).mpr (by simpa [mul_comm] using logs)
  have AL : (n:ℝ)+1≤Real.log N/X := by
    have h := Ka.trans LK
    dsimp [A] at h
    linarith
  obtain ⟨dh,bd⟩ := graphDimension_residual X N Xp oneN n AL
  let m := graphDimension X N-(n+1)
  have mcut : cut≤(m:ℝ)/2 := by
    have l := (abs_le.mp bd).1
    have h := Ka.trans LK
    dsimp [A] at h
    change -(↑n+1:ℝ) ≤ (m:ℝ)-Real.log N/X at l
    linarith
  obtain ⟨mp,mt,err⟩ := law m mcut E (dim.trans dh)
  have p0 := ENNReal.toReal_pos mp.ne' mt.ne
  have mp' : 0<(m:ℝ) := by linarith only [cp,mcut]
  have m0 : 0<m := by exact_mod_cast mp'
  have Kr' : A*(|R|+ε)≤ε*(Real.log N/X) := by
    have h := (div_le_iff₀ ep).mp (Kr.trans LK)
    simpa [mul_comm] using h
  have b := scaled_rate_error R X N A ε Xp oneN m ep bd Kr' _ p0 err m0
  have e : 3*ε/X=δ := by dsimp [ε]; field_simp
  rw [e] at b
  have rc : R/X=Real.log M.det/(2*X) := by dsimp [R]; ring
  rw [rc] at b
  obtain ⟨low,high⟩ := abs_le.mp b
  rw [Real.rpow_def_of_pos posN,Real.rpow_def_of_pos posN,
    ← Real.exp_log p0,Real.exp_le_exp,Real.exp_le_exp]
  constructor <;> linarith only [low,high,mul_sub (Real.log N) (Real.log M.det/(2*X)) δ,
    mul_add (Real.log N) (Real.log M.det/(2*X)) δ,mul_comm δ (Real.log N)]

#print axioms sphere_pattern_power_rates
end RobustFolkman.GeometricGap
