import PairedAllocation
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma real_mass_hasSum (T : I → Set X) (h : ∀ i, MeasurableSet (T i))
    (d : Pairwise (Disjoint on T)) :
    HasSum (fun i => μ.real (T i)) (μ.real (⋃ i, T i)) := by
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using
    (hasSum_integral_iUnion (μ := μ) (f := fun _ : X => (1:ℝ)) h d
      (integrable_const (1:ℝ)).integrableOn)

noncomputable def cellCapacity (P Q : I → Set X) (i : I) : ℝ :=
  min (μ.real (P i)) (μ.real (Q i))

lemma cellCapacity_nonneg (P Q : I → Set X) (i : I) :
    0≤cellCapacity μ P Q i :=
  le_min measureReal_nonneg measureReal_nonneg

theorem cellCapacity_summable (P Q : I → Set X) (mp : ∀ i, MeasurableSet (P i))
    (outer : Pairwise (Disjoint on fun i => P i ∪ Q i)) :
    Summable (cellCapacity μ P Q) := by
  have disP : Pairwise (Disjoint on P) := fun _ _ ne =>
    (outer ne).mono subset_union_left subset_union_left
  exact Summable.of_nonneg_of_le (cellCapacity_nonneg μ P Q) (fun _ => min_le_left _ _)
    (real_mass_hasSum μ P mp disP).summable

/-- Any desired mass up to twice the total paired capacity can be placed
on complementary pairs with load exactly half that mass at every good root. -/
theorem paired_fractional_allocation [Nonempty I]
    (W : Kernel X) (P Q : I → Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i ∪ Q i))
    (m : ℝ) (mn : 0≤m) (mcap : m ≤ 2 * ∑' i, cellCapacity μ P Q i) :
    ∃ D : X → ℝ, BMeas D ∧ (∀ x, 0≤D x ∧ D x≤1) ∧
      (∀ x∉(⋃ i, P i ∪ Q i), D x=0) ∧
      (∀ i x, (x∈P i →
        D x=(m/2/(∑' j, cellCapacity μ P Q j))*cellCapacity μ P Q i/μ.real (P i)) ∧
        (x∈Q i →
        D x=(m/2/(∑' j, cellCapacity μ P Q j))*cellCapacity μ P Q i/μ.real (Q i))) ∧
      (∫ x,D x ∂μ)=m ∧
      ∀ v, PairedRow μ W P Q v → load μ W D v=m/2 := by
  let L := ∑' i, cellCapacity μ P Q i
  let s := m/2/L
  let q (i : I) := s * cellCapacity μ P Q i
  have L0 : 0≤L := tsum_nonneg (cellCapacity_nonneg μ P Q)
  have s0 : 0≤s := div_nonneg (by positivity) L0
  have s1 : s≤1 := by
    by_cases h : L=0
    · simp [s,h]
    · exact (div_le_iff₀ (lt_of_le_of_ne L0 (Ne.symm h))).mpr (by change m≤2*L at mcap; linarith)
  have q0 (i : I) : 0≤q i := mul_nonneg s0 (cellCapacity_nonneg μ P Q i)
  have qle (i : I) : q i≤cellCapacity μ P Q i := by
    change s * cellCapacity μ P Q i ≤ _
    exact (mul_le_mul_of_nonneg_right s1 (cellCapacity_nonneg μ P Q i)).trans_eq (one_mul _)
  have hs := cellCapacity_summable μ P Q mp outer
  have hq : Summable q := hs.mul_left s
  have hmass : (∑' i, q i)=m/2 := by
    change (∑' i, s * cellCapacity μ P Q i)=m/2
    rw [hs.tsum_mul_left]
    change m/2/L*L=m/2
    by_cases h : L=0
    · have h0 : m=0 := by change m≤2*L at mcap; linarith
      simp [h,h0]
    · exact div_mul_cancel₀ _ h
  obtain ⟨D,dm,unit,off,sides,mass,row⟩ := paired_allocation_of_quotas μ W P Q mp mq inner outer
    q q0 (fun i => (qle i).trans (min_le_left _ _)) (fun i => (qle i).trans (min_le_right _ _)) hq
  refine ⟨D,dm,unit,off,sides,?_,?_⟩
  · rw [mass,hmass]; ring
  · intro v hv
    rw [row v hv,hmass]

#print axioms paired_fractional_allocation
end SparseHalfGraphon
