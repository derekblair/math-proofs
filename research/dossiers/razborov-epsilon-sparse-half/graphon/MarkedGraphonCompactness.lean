import AlignedLimits
import PaddedTowerScale
import PaddedTowerTables

open Set MeasureTheory Function Filter Topology
open scoped ENNReal
namespace SparseHalfGraphon

lemma cutBound_one {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ=1) (K J : Kernel X) : CutBound μ K J 1 := by
  apply L1_imp_cut
  have h := integral_mono (gap_integrable μ K J).abs
    (integrable_const (μ:=μ.prod μ) (1:ℝ)) (gapW_bound K J)
  simpa [integral_const, smul_eq_mul, Measure.real, ← Set.univ_prod_univ,
    Measure.prod_prod, hμ] using h

lemma scale_succ_le_double (n : ℕ) : canonicalScale n ≤ 2 * canonicalScale (n+1) := by
  have h1 : 0 < (n:ℝ)+1 := by positivity
  have h2 : 0 < (n:ℝ)+2 := by positivity
  unfold canonicalScale
  push_cast
  rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring, ← one_div, ← one_div, mul_one_div,
    div_le_div_iff₀ h1 h2]
  linarith

/-- Marked cut compactness of bounded symmetric kernels on arbitrary
probability spaces. Each aligned kernel has its own coupling to the
same fixed Lebesgue limit, and marks agree outside small mass. -/
theorem marked_graphon_compactness {X : ℕ → Type*} [∀ k, MeasurableSpace (X k)]
    (μ : ∀ k, Measure (X k)) [∀ k, IsFiniteMeasure (μ k)] (hμ : ∀ k, μ k univ = 1)
    (W : ∀ k, Kernel (X k)) {s : ℕ} (hs : 0 < s)
    (mark : ∀ k, X k → Fin s) (hmark : ∀ k, Measurable (mark k)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ L : Kernel UnitHalfOpen,
    ∃ d : UnitHalfOpen → Fin s, Measurable d ∧
      ∀ ε > 0, ∀ᶠ k in atTop,
        ∃ π : Measure (X (q k) × UnitHalfOpen),
          MeasurePreserving Prod.fst π (μ (q k)) ∧ MeasurePreserving Prod.snd π unitμ ∧
          π univ = 1 ∧ π.real (labelMismatch (mark (q k)) d) ≤ ε ∧
          CutBound π (pullKernel (W (q k)) Prod.fst measurable_fst)
            (pullKernel L Prod.snd measurable_snd) ε := by
  have hm (k : ℕ) : mass (μ k)=1 := by simp [mass,Measure.real,hμ]
  let cap := towerCapacity s canonicalFuel
  have existsA (k : ℕ) := shrinking_marked_tower (μ k) hs (mark k) (hmark k) (W k) (hm k)
  let A (k : ℕ) : PaddedTower (X:=X k) cap := (existsA k).choose
  have hA (k : ℕ) := (existsA k).choose_spec
  let J (k n : ℕ) := blockKernel (μ k) (W k) ((A k).label n) ((A k).measurable_label n)
  have hc (k n : ℕ) : CutBound (μ k) (W k) (J k n) (2*canonicalScale n) := by
    cases n with
    | zero =>
      intro S T hS hT
      exact (cutBound_one (μ k) (hμ k) (W k) (J k 0) S T hS hT).trans
        (by norm_num [canonicalScale])
    | succ n =>
      intro S T hS hT
      exact ((hA k).2 n S T hS hT).trans (scale_succ_le_double n)
  have hδ : Tendsto (fun n => 2*canonicalScale n) atTop (𝓝 0) := by
    simpa using canonicalScale_tendsto.const_mul (2:ℝ)
  obtain ⟨q,hq,L,d,hd,hrest⟩ := aligned_tower_compactness μ hμ W cap (fun k => (A k).parent)
    (fun k => towerTables (μ k) (W k) (hm k) (A k)) (fun k => (A k).label)
    (fun k => (A k).measurable_label) (fun k n x => ((A k).parent_exact n x).symm)
    (fun _ _ _ => rfl) J
    (fun k n x y => tower_table_block (μ k) (W k) (hm k) (A k) n x y)
    (fun n => 2*canonicalScale n) hδ hc
  refine ⟨q,hq,L,d,hd,?_⟩
  intro ε he
  filter_upwards [hrest ε he] with k hk
  have hlabel : (A (q k)).label 0 = mark (q k) := (hA (q k)).1
  obtain ⟨π,hp,hr,hπ,hmis,hcut⟩ := hk
  refine ⟨π,hp,hr,hπ,?_,hcut⟩
  exact hlabel ▸ hmis

#print axioms marked_graphon_compactness
end SparseHalfGraphon
