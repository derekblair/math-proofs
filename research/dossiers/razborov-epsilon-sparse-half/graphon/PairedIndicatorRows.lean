import PairedProfileCells

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (ω ν : Measure X) [IsFiniteMeasure ω] [IsFiniteMeasure ν]

lemma load_fiber_zero_or_one (K : Kernel X) (v : X) (P : Set X) :
    ((∫ x in P, K.W (v,x) ∂ω)=0 →
        (fun x => K.W (v,x)) =ᵐ[ω.restrict P] (fun _ => (0:ℝ))) ∧
    ((∫ x in P, K.W (v,x) ∂ω)=ω.real P →
        (fun x => K.W (v,x)) =ᵐ[ω.restrict P] (fun _ => (1:ℝ))) := by
  have ii := row_integrable (ω.restrict P) K v
  constructor
  · exact (integral_eq_zero_iff_of_nonneg (fun _ => K.nonneg _) ii).mp
  · intro h
    have H : (∫ x in P, (1:ℝ)-K.W (v,x) ∂ω)=0 := by
      rw [integral_sub (integrable_const _) ii,setIntegral_const,smul_eq_mul,mul_one,h,sub_self]
    have HH := (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (K.le_one (v,x)))
      ((integrable_const (1:ℝ)).sub ii)).mp H
    filter_upwards [HH] with x e
    change 1-K.W (v,x)=0 at e
    linarith

/-- A complementary full/zero row integral on positive cells comes from
one common measurable anchor partition, with exact 0/1 values a.e. -/
theorem paired_indicator_partition (K : Kernel X) (P Q : Set X)
    (hp : 0<ω.real P)
    (h : ∀ᵐ v ∂ν,
      ((∫ x in P,K.W (v,x) ∂ω)=ω.real P ∧ (∫ x in Q,K.W (v,x) ∂ω)=0) ∨
      ((∫ x in P,K.W (v,x) ∂ω)=0 ∧ (∫ x in Q,K.W (v,x) ∂ω)=ω.real Q)) :
    ∃ A : Set X, MeasurableSet A ∧
      (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict P] (fun _ => A.indicator (fun _=>(1:ℝ)) v)) ∧
      (∀ᵐ v ∂ν, (fun x=>K.W (v,x)) =ᵐ[ω.restrict Q] (fun _ => Aᶜ.indicator (fun _=>(1:ℝ)) v)) := by
  classical
  let A : Set X := {v | deg (ω.restrict P) K v = ω.real P}
  have am : MeasurableSet A := measurableSet_eq_fun (deg_measurable _ K) measurable_const
  refine ⟨A,am,?_,?_⟩
  · filter_upwards [h] with v hv
    rcases hv with ⟨p,_⟩|⟨p,_⟩
    · have a : v∈A := p
      rw [indicator_of_mem a]
      exact (load_fiber_zero_or_one ω K v P).2 p
    · have a : v∉A := by
        intro e
        change (∫ x in P,K.W (v,x) ∂ω)=ω.real P at e
        linarith
      rw [indicator_of_notMem a]
      exact (load_fiber_zero_or_one ω K v P).1 p
  · filter_upwards [h] with v hv
    rcases hv with ⟨p,q⟩|⟨p,q⟩
    · have a : v∈A := p
      have ac : v∉Aᶜ := by simpa
      rw [indicator_of_notMem ac]
      exact (load_fiber_zero_or_one ω K v Q).1 q
    · have a : v∈Aᶜ := by
        intro e
        change (∫ x in P,K.W (v,x) ∂ω)=ω.real P at e
        linarith
      rw [indicator_of_mem a]
      exact (load_fiber_zero_or_one ω K v Q).2 q

#print axioms paired_indicator_partition
end SparseHalfGraphon
