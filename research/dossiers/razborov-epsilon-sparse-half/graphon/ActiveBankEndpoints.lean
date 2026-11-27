import ActiveBankRectangles
import GreedyEligible
import RigidityTransferLabels
import PetersenKernel

open Set MeasureTheory Function Filter
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
variable {K : Kernel Y} {A : Set Y} {I : Type*} (B : ActiveBank μ K A I)

theorem anchor_zero_of_energy (m : MeasurableSet A)
    (h : energyPair μ K (indicatorWeight A) (indicatorWeight A)=0) :
    ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0 := by
  have ha := indicatorWeight_unit A m
  have he := reweight_energy μ K _ _ ha.1 ha.1 (fun x=>(ha.2 x).1) (fun x=>(ha.2 x).1)
    (fun x=>(ha.2 x).2) (fun x=>(ha.2 x).2)
  rw [indicatorWeight_reweight μ A m,h] at he
  exact (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ K.nonneg)
    (integrable_bounded _ K.measurable_W K.nonneg K.le_one)).mp he

/-- Large isolate case of actual graphon rigidity. -/
theorem ActiveBank.c5_of_single_full (hA : MeasurableSet A) (hAm : μ.real A=2/5)
    (hμ : μ.real univ=1)
    (hZ : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (hb : 1/50≤beta μ K) (j : I) (hp : B.p j=2) (hq : B.q j=2)
    (hrest : ∀ k≠j, B.p k=0) :
    ∃ g : Y→Fin 5, Measurable g ∧ (∀ i,μ.real (cell g i)=1/5) ∧
      K.W =ᵐ[μ.prod μ] (fun z=>edgeReal (C5Stability.adj (g z.1) (g z.2))) := by
  have ⟨p,q⟩ := B.equal_caps j 2 hp hq
  have p1 : μ.real (B.P j)=1/5 := by linarith
  have q1 : μ.real (B.Q j)=1/5 := by linarith
  have pa : Disjoint A (B.P j) := Set.disjoint_left.mpr
    (fun _ hx hy => (B.inside j (Or.inl hy)) hx)
  have qa : Disjoint A (B.Q j) := Set.disjoint_left.mpr
    (fun _ hx hy => (B.inside j (Or.inr hy)) hx)
  have rr := B.anchor_half j (by rw [p1]; norm_num) hAm
  rw [measureReal_restrict_apply (B.meas j).2.2,inter_comm] at rr
  have out : ∀ᵐ z ∂(μ.restrict Aᶜ).prod (μ.restrict Aᶜ), K.W z=0 ∨
      (z.1∈B.P j ∧ z.2∈B.Q j) ∨ (z.1∈B.Q j ∧ z.2∈B.P j) := by
    classical
    filter_upwards [B.edge] with z hz
    by_cases h : K.W z=0
    · exact Or.inl h
    · obtain ⟨k,hk⟩ := hz (lt_of_le_of_ne (K.nonneg _) (Ne.symm h))
      by_cases e:k=j
      · exact Or.inr (e ▸ hk)
      · have ⟨he,hf⟩ := B.empty_of_p_zero k (hrest k e)
        simp [he,hf] at hk
  have he := SparseHalfCountableEndpoint.large_isolate_cycle μ K A (B.R j) (B.P j) (B.Q j)
    hA (B.meas j).2.2 (B.meas j).1 (B.meas j).2.1 pa qa (B.inner j)
    hμ hAm rr p1 q1 hZ (B.cross_rect j false) (B.cross_rect j true) out
  rcases he with ⟨H,hH⟩ | hK
  · exact False.elim ((not_lt_of_ge (hb.trans (csInf_le (range_bdd μ K) ⟨H,rfl⟩))) hH)
  · have hCells := SparseHalfCountableEndpoint.isolate_cells A (B.R j) (B.P j) (B.Q j)
      hA (B.meas j).2.2 (B.meas j).1 (B.meas j).2.1 pa qa (B.inner j)
    have hM := SparseHalfCountableEndpoint.isolate_mass μ A (B.R j) (B.P j) (B.Q j)
      hA (B.meas j).2.2 (B.meas j).1 (B.meas j).2.1 pa qa (B.inner j) hμ hAm rr p1 q1
    exact SparseHalfCountableEndpoint.isolate_label_for_transfer μ K A (B.R j) (B.P j) (B.Q j) hCells hM hK

#print axioms ActiveBank.c5_of_single_full
end SparseHalfGraphon
