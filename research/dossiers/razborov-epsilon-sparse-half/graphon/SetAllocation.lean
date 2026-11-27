import RootSupport

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Select any specified mass fractionally from a measurable set,
without requiring atomlessness. -/
noncomputable def allocSet (S : Set X) (q : ℝ) : X→ℝ :=
  S.indicator (fun _ => q/μ.real S)

lemma allocSet_bmeas (S : Set X) (hS : MeasurableSet S) (q : ℝ)
    (h0 : 0≤q) (hq : q≤μ.real S) : BMeas (allocSet μ S q) := by
  classical
  refine BMeas.of_unit (measurable_const.indicator hS) ?_ ?_
  · intro x
    by_cases hx : x∈S
    · simpa [allocSet,hx] using div_nonneg h0 (measureReal_nonneg (μ:=μ) (s:=S))
    · simp [allocSet,hx]
  · intro x
    by_cases hx : x∈S
    · have hl : q/μ.real S≤1 := by
        by_cases h : μ.real S=0
        · simp [h]
        · exact (div_le_iff₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm h))).mpr (by simpa using hq)
      simpa [allocSet,hx] using hl
    · simp [allocSet,hx]

lemma allocSet_nn (S : Set X) (q : ℝ) (h0 : 0≤q) (x : X) :
    0≤allocSet μ S q x := by
  classical
  by_cases hx : x∈S
  · simpa [allocSet,hx] using div_nonneg h0 (measureReal_nonneg (μ:=μ) (s:=S))
  · simp [allocSet,hx]

lemma allocSet_le (S : Set X) (q : ℝ) (hq : q≤μ.real S) (x : X) :
    allocSet μ S q x≤1 := by
  classical
  by_cases hx : x∈S
  · have hl : q/μ.real S≤1 := by
      by_cases h : μ.real S=0
      · simp [h]
      · exact (div_le_iff₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm h))).mpr (by simpa using hq)
    simpa [allocSet,hx] using hl
  · simp [allocSet,hx]

lemma allocSet_mass (S : Set X) (hS : MeasurableSet S) (q : ℝ) (h0 : 0≤q)
    (hq : q≤μ.real S) : (∫ x,allocSet μ S q x ∂μ)=q := by
  rw [allocSet,integral_indicator hS,setIntegral_const,smul_eq_mul]
  by_cases h : μ.real S=0
  · have hq0 : q=0 := by linarith
    simp [h,hq0]
  · exact (mul_comm _ _).trans (div_mul_cancel₀ _ h)

lemma allocSet_support (S : Set X) (q : ℝ) {x : X} (h : x∉S) :
    allocSet μ S q x=0 := by simp [allocSet,h]

lemma allocSet_pos (S : Set X) (q : ℝ) (h0 : 0<q) (hq : q≤μ.real S) {x : X}
    (hx : x∈S) : 0<allocSet μ S q x := by
  simpa [allocSet,hx] using (div_pos h0 (h0.trans_le hq))

#print axioms allocSet_mass
end SparseHalfGraphon
