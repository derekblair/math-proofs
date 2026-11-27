import StepEnergy

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable {I : Type*} [Fintype I]
variable (P : I→Set X) (e : I→I→Bool)
variable (μ : Measure X) [IsFiniteMeasure μ]

theorem step_rigidity (B : Cells P) (sym : ∀ i j,e i j=e j i)
    (K : Kernel X) (cover : ∀ᵐ x ∂μ, ∃ i,x∈P i)
    (zeros : ∀ i j,e i j=false →
      ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)),K.W z=0)
    (testers : ∀ i j,e i j=true → ∃ q : I→ℝ,
      (∀ k,0≤q k ∧ q k≤μ.real (P k)) ∧ (∑ k,q k)=1/2 ∧
      0<q i ∧ 0<q j ∧
      (∑ a : I×I, q a.1*q a.2*(if e a.1 a.2 then 1 else 0))/2≤1/50) :
    (∃ H : Half μ, halfEnergy μ K H<1/50) ∨
      K.W =ᵐ[μ.prod μ] (stepKernel P e B sym).W := by
  classical
  let J := stepKernel P e B sym
  have major := dominated_step P e μ B sym K cover zeros
  by_cases all : ∀ i j,e i j=true →
      ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)), K.W z=1
  · right
    have local_eq (i j : I) : ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)), K.W z=J.W z := by
      have mem : ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)), z∈P i ×ˢ P j := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem ((B.meas i).prod (B.meas j))
      cases E : e i j
      · filter_upwards [mem, zeros i j E] with z hz hk
        rw [hk,show J.W z=stepW P e z from rfl]
        rcases z with ⟨a,b⟩
        rw [stepW_on P e B i j hz.1 hz.2,E]
        rfl
      · filter_upwards [mem, all i j E] with z hz hk
        rw [hk,show J.W z=stepW P e z from rfl]
        rcases z with ⟨a,b⟩
        rw [stepW_on P e B i j hz.1 hz.2,E]
        rfl
    have bound (i j : I) : ∀ᵐ z ∂μ.prod μ, z.1∈P i → z.2∈P j → K.W z=J.W z := by
      have t := local_eq i j
      rw [Measure.prod_restrict,ae_restrict_iff' ((B.meas i).prod (B.meas j))] at t
      exact t.mono fun z hz hi hj => hz ⟨hi,hj⟩
    have both := ae_all_iff.2 (fun i => ae_all_iff.2 (bound i))
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=μ)).ae cover,
      (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=μ)).ae cover,both] with z ⟨i,hi⟩ ⟨j,hj⟩ hz
    exact hz i j hi hj
  · left
    push Not at all
    obtain ⟨i,j,E,missing⟩ := all
    obtain ⟨q,hq,mass,qi,qj,cost⟩ := testers i j E
    let H := stepHalf P μ B q hq mass
    have tight : halfEnergy μ J H≤1/50 := (step_energy P e μ B sym q hq mass).trans_le cost
    have pos (k : I) (qk : 0<q k) (x : X) (hx : x∈P k) : 0<H.f x := by
      change 0<stepAllocation P μ q x
      rw [stepAllocation_on P μ B q hx]
      exact div_pos qk (qk.trans_le (hq k).2)
    have full : ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)), J.W z=1 := by
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem ((B.meas i).prod (B.meas j))] with ⟨x,y⟩ ⟨hx,hy⟩
      change stepW P e (x,y)=1
      rw [stepW_on P e B i j hx hy,E]
      rfl
    exact ⟨H,strict_of_missing_rectangle_pos μ K J H (P i) (P j) (B.meas i) (B.meas j)
      major tight (pos i qi) (pos j qj) full (fun h => missing (h.mono (fun _ e => not_not_intro e)))⟩

#print axioms step_rigidity
end SparseHalfCountableEndpoint
