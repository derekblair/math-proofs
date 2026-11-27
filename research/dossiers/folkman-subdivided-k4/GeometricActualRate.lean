import GeometricSpherePatternRate

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

variable {n : ℕ}

/-- The determinant rate is the actual threshold-pattern probability
rate in the iid spherical graph, not just a formal density integral.
One cutoff works for any real Hilbert space of the indicated dimension. -/
theorem sphere_pattern_rate (C : Fin n→Fin n→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (small : n≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (M : Matrix (Fin n) (Fin n) ℝ) (mf : GramFeasible C t M)
    (max : ∀ A, GramFeasible C t A → A.det≤M.det) (ε : ℝ) (ep : 0<ε) :
    ∃ cutoff : ℝ, 0<cutoff ∧ ∀ (m : ℕ), cutoff≤(m:ℝ)/2 →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
        Module.finrank ℝ E=n+m+1 →
        0<spherePatternMass (E:=E) C t ∧ spherePatternMass (E:=E) C t < ∞ ∧
        |Real.log (spherePatternMass (E:=E) C t).toReal / (m:ℝ)-Real.log M.det/2|≤ε := by
  have nc : Fintype.card (Fin n) ≤ 6 := by simpa using small
  obtain ⟨cut,cp,law⟩ := normalized_determinant_log_rate C sym nc t t0 ts M mf max (2*ε) (by positivity)
  refine ⟨cut,cp,?_⟩
  intro m ml E _ _ _ _ _ _ dim
  have pp : 0<(m:ℝ)/2 := cp.trans_le ml
  have mp : 0<(m:ℝ) := by linarith
  have mm : 0<m := by exact_mod_cast mp
  obtain ⟨fp,ft,dp,dt,bd⟩ := law ((m:ℝ)/2) ml
  rw [sphere_pattern_mass_integrals n m mm dim C t]
  refine ⟨ENNReal.div_pos fp.ne' dt.ne, ENNReal.div_lt_top ft.ne dp.ne',?_⟩
  rw [ENNReal.toReal_div,Real.log_div
    (ENNReal.toReal_pos fp.ne' ft.ne).ne' (ENNReal.toReal_pos dp.ne' dt.ne).ne']
  let a := Real.log (patternIntegral C t ((m:ℝ)/2)).toReal -
    Real.log (patternIntegral (I:=Fin n) (fun _ _ => False) (1/40000) ((m:ℝ)/2)).toReal
  change |a/(m:ℝ)-Real.log M.det/2|≤ε
  have z : (a/((m:ℝ)/2)-Real.log M.det)/2=a/(m:ℝ)-Real.log M.det/2 := by
    field_simp
  rw [← z,abs_div,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  exact (div_le_iff₀ (by norm_num : 0<(2:ℝ))).mpr (by simpa [a,mul_comm] using bd)

theorem sphere_pattern_rate_exp (C : Fin n→Fin n→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (small : n≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (M : Matrix (Fin n) (Fin n) ℝ) (mf : GramFeasible C t M)
    (max : ∀ A, GramFeasible C t A → A.det≤M.det) (ε : ℝ) (ep : 0<ε) :
    ∃ cutoff : ℝ, 0<cutoff ∧ ∀ (m : ℕ), cutoff≤(m:ℝ)/2 →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
        Module.finrank ℝ E=n+m+1 →
        Real.exp ((m:ℝ)*(Real.log M.det/2-ε)) ≤ (spherePatternMass (E:=E) C t).toReal ∧
        (spherePatternMass (E:=E) C t).toReal ≤ Real.exp ((m:ℝ)*(Real.log M.det/2+ε)) := by
  obtain ⟨c,cp,law⟩ := sphere_pattern_rate C sym small t t0 ts M mf max ε ep
  refine ⟨c,cp,?_⟩
  intro m ml E _ _ _ _ _ _ d
  obtain ⟨p,pt,b⟩ := law m ml E d
  have pr := ENNReal.toReal_pos p.ne' pt.ne
  have mp : 0<(m:ℝ) := by linarith only [cp,ml]
  obtain ⟨l,u⟩ := abs_le.mp b
  have l' : Real.log M.det/2-ε ≤ Real.log (spherePatternMass (E:=E) C t).toReal/(m:ℝ) := by linarith
  have u' : Real.log (spherePatternMass (E:=E) C t).toReal/(m:ℝ)≤Real.log M.det/2+ε := by linarith
  constructor
  · rw [← Real.exp_log pr, Real.exp_le_exp]
    simpa [mul_comm] using (le_div_iff₀ mp).mp l'
  · rw [← Real.exp_log pr, Real.exp_le_exp]
    simpa [mul_comm] using (div_le_iff₀ mp).mp u'

#print axioms sphere_pattern_rate_exp
end RobustFolkman.GeometricGap
