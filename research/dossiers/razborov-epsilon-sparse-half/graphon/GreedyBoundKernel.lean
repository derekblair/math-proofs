import GreedyCaseOneKernel

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma neighbor_allocation_zero_point (W : Kernel X)
    (ht : ∀ z, triangle W z=0) (D : X→ℝ) (v : X) :
    energyPair μ W (fun x=>D x*W.W (v,x)) (fun x=>D x*W.W (v,x))=0 := by
  unfold energyPair
  have h : (fun z : X×X=> (D z.1*W.W (v,z.1))*(D z.2*W.W (v,z.2))*W.W z) = 0 := by
    funext z
    calc
      _ = D z.1*D z.2*triangle W (z,v) := by
        unfold triangle
        rw [W.symm z.1 v,W.symm z.2 v]
        ring
      _ = 0 := by rw [ht,mul_zero]
  rw [h]
  exact integral_zero _ _

/-- Combine the two exact kernel cases into a uniform loss with marked growth.
Only the degree interval and availability of the eligible allocation are needed. -/
theorem greedy_bound_kernel (W : Kernel X) (B D : X→ℝ)
    (hB : Measurable B) (hD : Measurable D)
    (hB0 : ∀ x,0≤B x) (hD0 : ∀ x,0≤D x) (hCap : ∀ x,B x+D x≤1)
    (a b : ℝ) (ha : 39/100≤a) (ha' : a<1/2) (hab : a≤b) (hb : b≤1/2)
    (hBm : (∫ x,B x ∂μ)=b) (hDm : (∫ x,D x ∂μ)=1-a-b)
    (hBB : energyPair μ W B B/2≤(1/2-a)*(b-a))
    (ht : ∀ z, triangle W z=0)
    (hd : ∀ x,0<D x→1/2-a≤deg (reweight μ B) W x ∧ deg (reweight μ B) W x≤b/2) :
    beta μ W ≤ a*(1/2-a)/2-(3/100)*(b-a) := by
  have hB1 x : B x≤1 := by linarith [hCap x,hD0 x]
  have hD1 x : D x≤1 := by linarith [hCap x,hB0 x]
  let ν := reweight μ B
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (reweight_le μ B hB1)
  let c := 2*(∫ x,D x*deg ν W x ∂μ)
  have hc : (∫ x,D x*deg ν W x ∂μ)=c/2 := by dsimp [c]; ring
  have cCap : c≤b*(1-a-b) := by
    have hd' := BMeas.of_unit hD hD0 hD1
    have hh := integral_mono
      (bMeas_integrable μ (hd'.mul (deg_bmeas ν W)))
      ((bMeas_integrable μ hd').const_mul (b/2)) (fun x => by
        change D x*deg ν W x ≤ (b/2)*D x
        by_cases h : D x=0
        · simp [h]
        · rw [mul_comm (b/2)]
          exact mul_le_mul_of_nonneg_left (hd x (lt_of_le_of_ne (hD0 x) (Ne.symm h))).2 (hD0 x))
    rw [integral_const_mul,hDm] at hh
    change (∫ x,D x*deg ν W x ∂μ)≤b/2*(1-a-b) at hh
    linarith [hc]
  have hg := greedy_loss_near_endpoint a b c ha hab cCap
  by_cases H : ∃ v, 1/2-b≤load μ W D v
  · obtain ⟨v,hv⟩ := H
    have h1 := greedy_kernel_case_one μ W B D hB hD hB0 hD0 hCap a b hb hBm hBB
      (fun x h=>(hd x h).2) v hv (neighbor_allocation_zero_point μ W ht D v)
    exact h1.trans ((le_max_left _ _).trans hg)
  · have hL : ∀ᵐ v ∂reweight μ B, load μ W D v≤1/2-b :=
      ae_of_all _ (fun v=>(lt_of_not_ge (fun hv=>H ⟨v,hv⟩)).le)
    have h2 := greedy_kernel_case_two μ W B D hB hD hB0 hD0 hCap a b c ha'
      (by linarith) hBm hDm hBB (ae_of_all _ ht) hd hL hc
    exact h2.trans ((le_max_right _ _).trans hg)

#print axioms greedy_bound_kernel
end SparseHalfGraphon
