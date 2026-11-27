import CouplingEditRound
import CutExceptional
import FiniteKernelHalf
import StabilityExamples

open MeasureTheory Set Function Filter Topology
open scoped BigOperators ENNReal
namespace SparseHalfGraphon
open SparseHalfStability

theorem cut_replace_ae_right {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (K L J : Kernel X) (ε : ℝ)
    (h : L.W =ᵐ[μ.prod μ] J.W) (cut : CutBound μ K L ε) :
    CutBound μ K J ε := by
  have gap : gapW L J =ᵐ[μ.prod μ] (fun _ => 0) := by
    filter_upwards [h] with z hz
    simp [gapW,hz]
  have zero : (∫ z, |gapW L J z| ∂μ.prod μ) ≤ 0 := by
    have hh : (fun z => |gapW L J z|) =ᵐ[μ.prod μ] (fun _ => 0) := by
      filter_upwards [gap] with z hz
      simp [hz]
    rw [integral_congr_ae hh]
    simp
  simpa using cut_tri μ K L J ε 0 cut (L1_imp_cut μ L J 0 zero)

theorem pull_W_ae_of_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (p : X→Y) (hp : MeasurePreserving p μ ν) (L J : Kernel Y) (h : L.W =ᵐ[ν.prod ν] J.W) :
    (pullKernel L p hp.measurable).W =ᵐ[μ.prod μ] (pullKernel J p hp.measurable).W :=
  (hp.prod hp).quasiMeasurePreserving.ae_eq_comp h

private theorem edgeReal_boolReal (b : Bool) : edgeReal b = boolReal b := rfl

/-- An eventual binary cut limit can be rounded into a single accurate
finite labeling, and in fact all sufficiently large samples have one.
An a.e. binary presentation of the limit is enough. -/
theorem binary_limit_has_edit_labeling {V : ℕ→Type*}
    [∀ k, Fintype (V k)] [∀ k, MeasurableSpace (V k)] [∀ k, MeasurableSingletonClass (V k)]
    [∀ k, DecidableEq (V k)]
    {Y I : Type*} [MeasurableSpace Y] [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [DecidableEq I]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (G : ∀ k, V k→V k→Bool) (sym : ∀ k u v, G k u v=G k v u)
    (gl : ∀ k v, G k v v=false)
    (B : I→I→Bool) (bs : ∀ u v, B u v=B v u) (bl : ∀ i, B i i=false)
    (L : Kernel Y) (g : Y→I) (hg : Measurable g)
    (binary : L.W =ᵐ[ν.prod ν] (fun z => edgeReal (B (g z.1) (g z.2))))
    (size : Tendsto (fun k => Fintype.card (V k)) atTop atTop)
    (ha : ∀ ε>0, ∀ᶠ k in atTop, ∃ π : Measure (V k×Y),
      MeasurePreserving Prod.fst π uniformVertices ∧ MeasurePreserving Prod.snd π ν ∧ π univ=1 ∧
      CutBound π (pullKernel (adjacencyKernel (G k) (sym k)) Prod.fst measurable_fst)
        (pullKernel L Prod.snd measurable_snd) ε)
    (a : ℝ) (ap : 0<a) :
    ∀ᶠ k in atTop, ∃ q : V k→I,
      (∀ i, |((fiber q i).card : ℝ)/(Fintype.card (V k) : ℝ)-ν.real (cell g i)| ≤ a) ∧
      ((directedErrors (G k) B q).card : ℝ)/(Fintype.card (V k) : ℝ)^2 ≤ a^2 := by
  let m : ℝ := Fintype.card I
  let ε : ℝ := a^2/(2*(m^2+1))
  have ep : 0<ε := by unfold ε; positivity
  have hε : m^2*ε ≤ a^2/2 := by
    unfold ε
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0<2*(m^2+1))]
    nlinarith [sq_nonneg a]
  have hN0 := exists_nat_gt (2*m/a^2)
  obtain ⟨N,hN⟩ := hN0
  have pos : ∀ᶠ k in atTop, 0<Fintype.card (V k) := size.eventually (eventually_gt_atTop 0)
  have large : ∀ᶠ k in atTop, N≤Fintype.card (V k) := size.eventually (eventually_ge_atTop N)
  filter_upwards [pos,large,ha ε ep] with k kp kn ⟨π,hp,hq,hπ,cut⟩
  letI : IsFiniteMeasure π := ⟨by rw [hπ]; exact ENNReal.one_lt_top⟩
  let T := pullKernel (adjacencyKernel B bs) g hg
  have eq : L.W =ᵐ[ν.prod ν] T.W := binary
  have cut' := cut_replace_ae_right π _ _ _ ε (pull_W_ae_of_preserving π ν Prod.snd hq L T eq) cut
  have mn : 0 < (Fintype.card (V k) : ℝ) := by exact_mod_cast kp
  have aq : 0 < a^2 := pow_pos ap 2
  have nlarge : 2*m/a^2 ≤ (Fintype.card (V k) : ℝ) :=
    hN.le.trans (by exact_mod_cast kn)
  have hvar : m/(Fintype.card (V k) : ℝ) ≤ a^2/2 := by
    apply (div_le_iff₀ mn).mpr
    have b := (div_le_iff₀ aq).mp nlarge
    nlinarith only [b]
  have bud : m^2*ε + m/(Fintype.card (V k) : ℝ) ≤ a^2 := by linarith
  let gc : V k×Y→I := g ∘ Prod.snd
  have unif (v : V k) : π.real (cell Prod.fst v) = 1/(Fintype.card (V k) : ℝ) := by
    rw [real_cell_preserving π uniformVertices Prod.fst hp, uniform_singleton]
  have mp (i : I) : |π.real (cell gc i)-ν.real (cell g i)| ≤ 0 := by
    rw [real_cell_comp_preserving π ν Prod.snd hq g hg i]
    simp
  have q := coupling_cut_round π Prod.fst gc hp.measurable (hg.comp hq.measurable)
    kp unif (G k) B (gl k) bl _ _ ε cut'
    (fun _ _ => edgeReal_boolReal _) (fun _ _ => edgeReal_boolReal _)
    (fun i => ν.real (cell g i)) a 0 ap.le mp bud
  simpa only [fiber,directedErrors,add_zero] using q

#print axioms binary_limit_has_edit_labeling
end SparseHalfGraphon
