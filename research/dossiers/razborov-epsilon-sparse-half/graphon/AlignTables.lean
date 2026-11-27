import UnitStepLimit
import LabelCouplingReal

open Set MeasureTheory Function Filter Topology
open scoped ENNReal BigOperators
namespace SparseHalfGraphon

variable {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
variable [∀ n, MeasurableSpace (I n)] [∀ n, MeasurableSingletonClass (I n)]
variable {p : ∀ n, I (n+1) → I n} (B : CoherentTables I p)

lemma unitLabel_positive (n : ℕ) (y : UnitHalfOpen) :
    0 < B.cell n (B.unitLabel n y) := by
  obtain ⟨h₁,h₂⟩ := B.unitLabel_mem n y
  linarith only [h₁,h₂]

/-- At each fixed level, couple the sample steps to the realizing
interval steps. Labels of zero limiting mass occur nowhere on the
half-open interval, so no positive-denominator limit is used there. -/
theorem align_fixed_level {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (μ : ∀ k, Measure (X k)) [∀ k, IsFiniteMeasure (μ k)] (hm : ∀ k, μ k univ = 1)
    {P : ℕ → ∀ n, I (n+1) → I n} (A : ∀ k : ℕ, CoherentTables I (P k)) (n : ℕ)
    (c : ∀ k, X k → I n) (hc : ∀ k, Measurable (c k)) (J : ∀ k, Kernel (X k))
    (hμc : ∀ k i, (μ k).real (cell (c k) i) = (A k).cell n i)
    (hJ : ∀ k x y, (J k).W (x,y) = (A k).density n (c k x) (c k y))
    (hC : ∀ i, Tendsto (fun k => (A k).cell n i) atTop (𝓝 (B.cell n i)))
    (hD : ∀ i j, Tendsto (fun k => (A k).joint n i j) atTop (𝓝 (B.joint n i j)))
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ k in atTop,
      ∃ π : Measure (X k × UnitHalfOpen), MeasurePreserving Prod.fst π (μ k) ∧
        MeasurePreserving Prod.snd π unitμ ∧ π univ = 1 ∧
        π.real (labelMismatch (c k) (B.unitLabel n)) ≤ ε ∧
        CutBound π (pullKernel (J k) Prod.fst measurable_fst)
          (pullKernel (B.unitStep n) Prod.snd measurable_snd) (3*ε) := by
  classical
  have hmin : Tendsto (fun k => ∑ i, min ((A k).cell n i) (B.cell n i)) atTop (𝓝 1) := by
    rw [← B.cell_total n]
    exact tendsto_finsetSum Finset.univ (fun i _ =>
      by simpa only [min_self] using (hC i).min (tendsto_const_nhds (x := B.cell n i)))
  have hm' := Metric.tendsto_nhds.mp hmin ε he
  have hd' : ∀ᶠ k in atTop, ∀ i j, 0 < B.cell n i → 0 < B.cell n j →
      |(A k).density n i j - B.density n i j| ≤ ε := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hi : 0 < B.cell n i
    · by_cases hj : 0 < B.cell n j
      · have hh := tendsto_table_density A B n i j hi hj (hC i) (hC j) (hD i j)
        exact (Metric.tendsto_nhds.mp hh ε he).mono (fun _ hk _ _ => by
          rw [Real.dist_eq] at hk
          exact hk.le)
      · exact Eventually.of_forall (fun _ _ hj' => (hj hj').elim)
    · exact Eventually.of_forall (fun _ hi' _ => (hi hi').elim)
  filter_upwards [hm',hd'] with k hmk hdk
  obtain ⟨π,h₁,h₂,hπ,hmismatch⟩ := matched_label_coupling_real (μ k) unitμ
    (hm k) unitμ_univ (c k) (B.unitLabel n) (hc k) (B.unitLabel_meas n)
  haveI : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
  have ha : mass π = 1 := by simp [mass,Measure.real,hπ]
  have hb : π.real (labelMismatch (c k) (B.unitLabel n)) ≤ ε := by
    have hμd (i : I n) : unitμ.real (cell (B.unitLabel n) i) = B.cell n i := B.unitLabel_mass n i
    simp only [hμc, hμd] at hmismatch
    rw [Real.dist_eq] at hmk
    linarith [neg_abs_le (∑ i, min ((A k).cell n i) (B.cell n i)-1)]
  refine ⟨π,h₁,h₂,hπ,hb,?_⟩
  let W : Kernel (X k × UnitHalfOpen) := pullKernel (J k) Prod.fst measurable_fst
  let U : Kernel (X k × UnitHalfOpen) := pullKernel (B.unitStep n) Prod.snd measurable_snd
  let S := labelMismatch (c k) (B.unitLabel n)
  have hS : MeasurableSet S := labelMismatch_meas (hc k) (B.unitLabel_meas n)
  have hgood (z w : X k × UnitHalfOpen) (hz : z ∉ S) (hw : w ∉ S) :
      |gapW W U (z,w)| ≤ ε := by
    have hz' : c k z.1 = B.unitLabel n z.2 := not_not.mp hz
    have hw' : c k w.1 = B.unitLabel n w.2 := not_not.mp hw
    change |(J k).W (z.1,w.1) - B.density n (B.unitLabel n z.2) (B.unitLabel n w.2)| ≤ ε
    rw [hJ, hz',hw']
    exact hdk _ _ (unitLabel_positive B n z.2) (unitLabel_positive B n w.2)
  have hh := exceptional_vertex_cut π W U S hS ha ε he.le hgood
  intro s t hs ht
  exact (hh s t hs ht).trans (by linarith only [hb])

#print axioms align_fixed_level
end SparseHalfGraphon
