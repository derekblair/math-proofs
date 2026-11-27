import KernelBlockMeans
import Mathlib.MeasureTheory.MeasurableSpace.Instances

open MeasureTheory Set Function
namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def bitOf (S : Set X) (x : X) : Bool := by
  classical exact if x∈S then true else false

lemma bit_meas (S : Set X) (hS : MeasurableSet S) : Measurable (bitOf S) := by
  classical
  exact measurable_const.ite hS measurable_const

noncomputable def refinedLabel (c : X→ι) (S T : Set X) (x : X) :
    ι×Bool×Bool := (c x,bitOf S x,bitOf T x)

lemma refine_meas (c : X→ι) (hc : Measurable c) (S T : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Measurable (refinedLabel c S T) :=
  hc.prodMk ((bit_meas S hS).prodMk (bit_meas T hT))

def rectangleTest (p : (ι×Bool×Bool)×(ι×Bool×Bool)) : ℝ :=
  if p.1.2.1 && p.2.2.2 then 1 else 0

lemma test_matches (c : X→ι) (S T : Set X) (z : X×X) :
    rectangleTest (pairLabel (refinedLabel c S T) z) =
      (S×ˢT).indicator (fun _ => (1:ℝ)) z := by
  classical
  by_cases hs : z.1∈S <;> by_cases ht : z.2∈T <;>
    simp [rectangleTest,pairLabel,refinedLabel,bitOf,hs,ht]

/-- One Frieze–Kannan refinement, with the marked cells retained and
at most four labels replacing each old label. -/
theorem weak_regular_step (K : Kernel X) (c : X→ι) (hc : Measurable c)
    (hμ : mass μ=1) (ε:ℝ) (hε : 0≤ε)
    (hfail : ¬CutBound μ K (blockKernel μ K c hc) ε) :
    ∃ S T : Set X, ∃ hS : MeasurableSet S, ∃ hT : MeasurableSet T,
      blockEnergy μ (blockKernel μ K c hc)+ε^2 <
        blockEnergy μ (blockKernel μ K (refinedLabel c S T) (refine_meas c hc S T hS hT)) := by
  classical
  unfold CutBound at hfail
  push_neg at hfail
  obtain ⟨S,T,hS,hT,hwitness⟩ := hfail
  refine ⟨S,T,hS,hT,?_⟩
  let d := refinedLabel c S T
  let hd := refine_meas c hc S T hS hT
  let J := blockKernel μ K c hc
  let p : (ι×Bool×Bool)×(ι×Bool×Bool)→ι×ι := fun z => (z.1.1,z.2.1)
  let g : X×X→ℝ := rectangleTest ∘ pairLabel d
  have hg : BMeas g := bmeas_comp_finite _ (pair_label_meas _ hd) _
  have hmass : mass (μ.prod μ)=1 := by
    unfold mass
    rw [← Set.univ_prod_univ,measureReal_prod_prod]
    change mass μ*mass μ=1
    simp [hμ]
  have hg₂ : (∫ z, (g z)^2 ∂μ.prod μ)≤1 := by
    have hpos := bMeas_integrable (μ.prod μ) hg.sq
    have he := integral_mono hpos (integrable_const (μ:=μ.prod μ) (1:ℝ)) (fun z => by
      change (rectangleTest (pairLabel d z))^2≤1
      unfold rectangleTest
      split <;> norm_num)
    rw [integral_const,smul_eq_mul,mul_one] at he
    change _≤mass (μ.prod μ) at he
    rwa [hmass] at he
  have hstep := refinement_witness (μ.prod μ) (pairLabel c) (pairLabel d) p
    (pair_label_meas c hc) (pair_label_meas d hd) (fun _ => rfl)
    K.W (BMeas.of_unit K.measurable_W K.nonneg K.le_one) rectangleTest hg₂
  have hG : Integrable (gapW K J) (μ.prod μ) :=
    (integrable_bounded (μ.prod μ) K.measurable_W K.nonneg K.le_one).sub
      (integrable_bounded (μ.prod μ) J.measurable_W J.nonneg J.le_one)
  have htest : (∫ z, (K.W z-J.W z)*g z ∂μ.prod μ) =
      ∫ x in S, ∫ y in T, K.W (x,y)-J.W (x,y) ∂μ ∂μ := by
    have hfun : (fun z => (K.W z-J.W z)*g z)=(S×ˢT).indicator (gapW K J) := by
      ext z
      change (K.W z-J.W z)*rectangleTest (pairLabel (refinedLabel c S T) z) = _
      rw [test_matches]
      by_cases hz : z∈S×ˢT
      · simp [Set.indicator_of_mem hz,gapW]
      · simp [Set.indicator_of_notMem hz]
    rw [hfun,integral_indicator (hS.prod hT),setIntegral_prod _ hG.integrableOn]
    rfl
  change (∫ z, (K.W z-J.W z)*g z ∂μ.prod μ)^2≤
    blockEnergy μ (blockKernel μ K d hd)-blockEnergy μ J at hstep
  rw [htest] at hstep
  change ε < |∫ x in S, ∫ y in T, K.W (x,y)-J.W (x,y) ∂μ ∂μ| at hwitness
  have ht := pow_lt_pow_left₀ hwitness hε (by norm_num : (2:ℕ)≠0)
  rw [sq_abs] at ht
  change blockEnergy μ J+ε^2<blockEnergy μ (blockKernel μ K d hd)
  linarith

#print axioms weak_regular_step
end SparseHalfGraphon
