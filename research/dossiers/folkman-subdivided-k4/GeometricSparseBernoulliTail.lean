import GeometricCapCount
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset
open scoped ENNReal
variable {S I : Type*} [MeasurableSpace S] [Fintype I] [DecidableEq I]

/-- A subset witness for a large count in iid coordinates.
There is no need to sum binomial probabilities over all large counts. -/
theorem retained_upper_tail (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S)
    (k : ℕ) :
    (Measure.pi (fun _ : I => σ)) {x : I → S | k≤(retained A x).card} ≤
      ((Fintype.card I).choose k : ℝ≥0∞)*(σ A)^k := by
  classical
  let L := (Finset.univ : Finset I).powersetCard k
  let E := fun J : Finset I => (J : Set I).pi (fun _ => A)
  have incl : {x : I→S | k≤(retained A x).card} ⊆ ⋃ J ∈ L, E J := by
    intro x hx
    rcases Finset.exists_subset_card_eq hx with ⟨J, hJ, hc⟩
    refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨Finset.mem_powersetCard.2
      ⟨Finset.subset_univ _,hc⟩,?_⟩⟩
    intro i hi
    have h := hJ hi
    simpa [retained] using h
  calc
    _ ≤ (Measure.pi (fun _ : I => σ)) (⋃ J ∈ L, E J) := measure_mono incl
    _ ≤ ∑ J ∈ L, (Measure.pi (fun _ : I => σ)) (E J) := measure_biUnion_finset_le _ _
    _ = _ := by
      have eq (J : Finset I) : (Measure.pi (fun _ : I => σ)) (E J)=(σ A)^J.card := by
        rw [Measure.pi_pi_finset]
        simp
      simp_rw [eq]
      rw [Finset.sum_congr rfl (fun J hJ => show (σ A)^J.card=(σ A)^k by
        rw [(Finset.mem_powersetCard.1 hJ).2])]
      simp [L,nsmul_eq_mul]

/-- Bounding one binomial coefficient by a positive generating function
gives an exponential tail at the expected-degree scale, not its square. -/
theorem sparse_choose_exp (n k : ℕ) (p : ℝ) (p0 : 0≤p) :
    (n.choose k : ℝ)*p^k ≤ Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k := by
  apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^k)).2
  by_cases kn : k≤n
  · have h : (2*p)^k * 1^(n-k) * (n.choose k : ℝ) ≤ (2*p+1)^n := by
      rw [add_pow]
      exact Finset.single_le_sum (f:=fun i => (2*p)^i * (1:ℝ)^(n-i) * (n.choose i : ℝ)) (fun i _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le kn))
    calc
      _ = (2*p)^k * 1^(n-k) * (n.choose k : ℝ) := by rw [mul_pow,one_pow]; ring
      _ ≤ (2*p+1)^n := h
      _ ≤ (Real.exp (2*p))^n := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge kn),Nat.cast_zero,zero_mul,zero_mul]
    positivity

theorem retained_upper_tail_exp (σ : Measure S) [IsProbabilityMeasure σ] (A : Set S) (k : ℕ) :
    (Measure.pi (fun _ : I => σ)).real {x : I → S | k≤(retained A x).card} ≤
      Real.exp (2*(Fintype.card I : ℝ)*(σ.real A))/(2:ℝ)^k := by
  have h := retained_upper_tail (I:=I) σ A k
  have fin : ((Fintype.card I).choose k : ℝ≥0∞)*(σ A)^k ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top (measure_ne_top σ _))
  have hr := ENNReal.toReal_mono fin h
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow] at hr
  exact hr.trans (sparse_choose_exp _ _ (σ.real A) ENNReal.toReal_nonneg)

#print axioms retained_upper_tail_exp
end RobustFolkman.GeometricGap
