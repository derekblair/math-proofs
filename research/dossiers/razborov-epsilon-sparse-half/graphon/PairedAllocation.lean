import AllocationLoads

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X I : Type*} [MeasurableSpace X] [Countable I] [Nonempty I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- An anchor root can choose either full side of each pair, independently. -/
def PairedRow (W : Kernel X) (P Q : I → Set X) (v : X) : Prop :=
  ∀ i, ((∫ x in P i, W.W (v,x) ∂μ) = μ.real (P i) ∧
        (∫ x in Q i, W.W (v,x) ∂μ) = 0) ∨
       ((∫ x in P i, W.W (v,x) ∂μ) = 0 ∧
        (∫ x in Q i, W.W (v,x) ∂μ) = μ.real (Q i))

lemma fraction_mul_measure (S : Set X) (q : ℝ)
    (hn : 0≤q) (hq : q≤μ.real S) : q/μ.real S * μ.real S=q := by
  by_cases h : μ.real S=0
  · have hq0 : q=0 := by linarith
    simp [h,hq0]
  · exact div_mul_cancel₀ _ h

/-- Each cell is used at the same prescribed mass from both sides, with constant
fractions on each side. Identical mass and root-load identities hold even
for infinitely many cells or null cells. -/
theorem paired_allocation_of_quotas
    (W : Kernel X) (P Q : I → Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i ∪ Q i))
    (q : I → ℝ) (qn : ∀ i, 0≤q i)
    (qp : ∀ i, q i≤μ.real (P i)) (qq : ∀ i, q i≤μ.real (Q i))
    (hsum : Summable q) :
    ∃ D : X → ℝ, BMeas D ∧ (∀ x, 0≤D x ∧ D x≤1) ∧
      (∀ x∉(⋃ i, P i ∪ Q i), D x=0) ∧
      (∀ i x, (x∈P i → D x=q i/μ.real (P i)) ∧ (x∈Q i → D x=q i/μ.real (Q i))) ∧
      (∫ x,D x ∂μ) = 2 * ∑' i, q i ∧
      ∀ v, PairedRow μ W P Q v → load μ W D v = ∑' i, q i := by
  classical
  let C (i : I) := P i ∪ Q i
  let U := ⋃ i, C i
  let g (i : I) := allocSet μ (P i) (q i) + allocSet μ (Q i) (q i)
  have mc (i : I) : MeasurableSet (C i) := (mp i).union (mq i)
  have mu : MeasurableSet U := MeasurableSet.iUnion mc
  have gm (i : I) : Measurable (g i) :=
    ((allocSet_bmeas μ _ (mp i) _ (qn i) (qp i)).1.add
      (allocSet_bmeas μ _ (mq i) _ (qn i) (qq i)).1)
  obtain ⟨d, dm, agree⟩ := exists_measurable_piecewise C mc g gm
    (fun i j ne x hx => False.elim (Set.disjoint_left.mp (outer ne) hx.1 hx.2))
  let D := U.indicator d
  have z (x) (hx : x∉U) : D x=0 := indicator_of_notMem hx _
  have dd (i x) (hx : x∈C i) : D x=g i x := by
    change U.indicator d x = _
    have hxU : x∈U := mem_iUnion.mpr ⟨i,hx⟩
    rw [indicator_of_mem hxU]
    exact agree i hx
  have sides (i x) : (x∈P i → D x=q i/μ.real (P i)) ∧
      (x∈Q i → D x=q i/μ.real (Q i)) := by
    constructor
    · intro hx
      rw [dd i x (Or.inl hx)]
      have ny : x∉Q i := fun hy => Set.disjoint_left.mp (inner i) hx hy
      simp [g,allocSet,hx,ny]
    · intro hx
      rw [dd i x (Or.inr hx)]
      have ny : x∉P i := fun hy => Set.disjoint_left.mp (inner i) hy hx
      simp [g,allocSet,hx,ny]
  have unit (x) : 0≤D x ∧ D x≤1 := by
    by_cases hx : x∈U
    · obtain ⟨i,hx⟩ := mem_iUnion.mp hx
      rcases hx with hp|hq
      · rw [(sides i x).1 hp, ←show allocSet μ (P i) (q i) x=q i/μ.real (P i) by simp [allocSet,hp]]
        exact ⟨allocSet_nn μ _ _ (qn i) _,allocSet_le μ _ _ (qp i) _⟩
      · rw [(sides i x).2 hq, ←show allocSet μ (Q i) (q i) x=q i/μ.real (Q i) by simp [allocSet,hq]]
        exact ⟨allocSet_nn μ _ _ (qn i) _,allocSet_le μ _ _ (qq i) _⟩
    · simp [z x hx]
  have dB : BMeas D := BMeas.of_unit (dm.indicator mu) (fun x => (unit x).1) (fun x => (unit x).2)
  have massSide (S : Set X) (hS : MeasurableSet S) (r : ℝ)
      (rn : 0≤r) (rq : r≤μ.real S) (de : ∀ x∈S, D x=r/μ.real S) :
      (∫ x in S, D x ∂μ)=r := by
    rw [setIntegral_congr_fun hS de,setIntegral_const,smul_eq_mul,mul_comm]
    exact fraction_mul_measure μ S r rn rq
  have split (f : X→ℝ) (hi : Integrable f μ) (off : ∀ x∉U, f x=0) :
      (∫ x,f x ∂μ)= ∑' i, ((∫ x in P i, f x ∂μ)+(∫ x in Q i, f x ∂μ)) := by
    have ff : U.indicator f=f := by
      ext x
      by_cases hx : x∈U <;> simp [hx,off]
    calc
      (∫ x,f x ∂μ) = ∫ x in U, f x ∂μ := by rw [← integral_indicator mu,ff]
      _ = ∑' i, ∫ x in C i, f x ∂μ := integral_iUnion mc outer hi.integrableOn
      _ = _ := by
        congr 1
        funext i
        exact setIntegral_union (inner i) (mq i) hi.integrableOn hi.integrableOn
  refine ⟨D,dB,unit,z,sides,?_,?_⟩
  · rw [split D (bMeas_integrable μ dB) z]
    simp_rw [massSide _ (mp _) _ (qn _) (qp _) (fun x hx => (sides _ x).1 hx),
      massSide _ (mq _) _ (qn _) (qq _) (fun x hx => (sides _ x).2 hx),←two_mul]
    exact hsum.tsum_mul_left 2
  · intro v h
    have bw : BMeas (fun x=>W.W (v,x)) :=
      BMeas.of_unit (rowMeasurable W v) (fun _ => W.nonneg _) (fun _ => W.le_one _)
    unfold load
    rw [split (fun x => D x * W.W (v,x)) (bMeas_integrable μ (dB.mul bw)) (fun x hx => by simp [z x hx])]
    congr 1
    funext i
    have E (S : Set X) (hS : MeasurableSet S) (de : ∀ x∈S, D x=q i/μ.real S) :
        (∫ x in S,D x*W.W (v,x) ∂μ)=(q i/μ.real S)*(∫ x in S,W.W (v,x) ∂μ) := by
      rw [setIntegral_congr_fun hS (fun x hx => congrArg (· * W.W (v,x)) (de x hx)),integral_const_mul]
    rw [E _ (mp i) (fun x hx => (sides i x).1 hx),E _ (mq i) (fun x hx => (sides i x).2 hx)]
    rcases h i with ⟨p,q'⟩|⟨p,q'⟩
    · simp [p,q',fraction_mul_measure μ _ _ (qn i) (qp i)]
    · simp [p,q',fraction_mul_measure μ _ _ (qn i) (qq i)]

#print axioms paired_allocation_of_quotas
end SparseHalfGraphon
