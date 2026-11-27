import GeometricFixedAnchors
import GeometricStrictGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped Pointwise InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem uniformSphere_subspace_null (K : Submodule ℝ E) (proper : K ≠ ⊤) :
    uniformSphere (volume : Measure E) {x : UnitSphere E | x.val∈K} = 0 := by
  let S : Set (UnitSphere E) := {x | x.val∈K}
  have ms : MeasurableSet S := K.closed_of_finiteDimensional.measurableSet.preimage measurable_subtype_coe
  rw [uniformSphere_cone_ratio volume S ms]
  have inclusion : coneOf S ⊆ (K : Set E) := by
    intro x hx
    obtain ⟨a,ha,b,hb,eq⟩ := Set.mem_smul.mp hx
    obtain ⟨u,hu,rfl⟩ := hb
    rw [← eq]
    exact K.smul_mem a hu
  have nul : (volume : Measure E) (K : Set E)=0 :=
    Measure.addHaar_submodule volume K proper
  have n : (volume : Measure E) (coneOf S)=0 :=
    le_antisymm ((measure_mono inclusion).trans_eq nul) bot_le
  simp [n]

theorem measurableSet_anchor_independent {I : Type*} [Fintype I] [DecidableEq I] :
    MeasurableSet {v : I→UnitSphere E | LinearIndependent ℝ (fun i => (v i).val)} := by
  have ev (i : I) : Continuous (fun v : I→UnitSphere E => (v i).val) :=
    continuous_subtype_val.comp (continuous_apply i)
  have C : Continuous (fun v : I→UnitSphere E => (anchorGram (fun i => (v i).val)).det) := by
    apply gram_det_continuous.comp
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (ev i).inner (ev j)
  have eq : {v : I→UnitSphere E | LinearIndependent ℝ (fun i => (v i).val)} =
      {v | (anchorGram (fun i => (v i).val)).det≠0} := by
    ext v
    exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜:=ℝ)).symm
  rw [eq]
  exact (isOpen_ne.preimage C).measurableSet

theorem ae_anchor_extension {k : ℕ} (v : Fin k→UnitSphere E)
    (vi : LinearIndependent ℝ (fun i => (v i).val))
    (di : k < Module.finrank ℝ E) :
    ∀ᵐ (x : UnitSphere E) ∂uniformSphere (volume : Measure E),
      LinearIndependent ℝ (Fin.snoc (fun i => (v i).val) (x : E)) := by
  let K := Submodule.span ℝ (Set.range (fun i => (v i).val))
  have kd : Module.finrank ℝ K=k := by
    simpa [K] using finrank_span_eq_card vi
  have p : K≠⊤ := by
    intro h
    rw [h,finrank_top] at kd
    omega
  have ae : ∀ᵐ (x : UnitSphere E) ∂uniformSphere (volume : Measure E), (x : UnitSphere E).val∉K := by
    rw [ae_iff]
    simpa only [not_not] using uniformSphere_subspace_null K p
  filter_upwards [ae] with x hx
  exact linearIndependent_finSnoc.mpr ⟨vi,hx⟩

#print axioms uniformSphere_subspace_null
#print axioms ae_anchor_extension
end RobustFolkman.GeometricGap
