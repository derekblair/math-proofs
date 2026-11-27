import GeometricSphereNull

namespace RobustFolkman.GeometricGap
open MeasureTheory MeasureTheory.Measure Set
variable {S : Type*} [MeasurableSpace S]

noncomputable def splitLast (k : ℕ) : (Fin (k+1)→S) ≃ᵐ ((Fin k→S)×S) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => S) (Fin.last k)).trans MeasurableEquiv.prodComm

theorem splitLast_apply (k : ℕ) (u : Fin (k+1) → S) :
    splitLast k u = (fun i => u i.castSucc, u (Fin.last k)) := by
  simp [splitLast,MeasurableEquiv.piFinSuccAbove]
  rfl

theorem splitLast_symm_apply (k : ℕ) (z : (Fin k→S)×S) :
    (splitLast k).symm z=Fin.snoc z.1 z.2 := by
  apply (splitLast k).injective
  rw [MeasurableEquiv.apply_symm_apply,splitLast_apply]
  simp

theorem splitLast_volume (μ : Measure S) [SigmaFinite μ] (k : ℕ) :
    MeasurePreserving (splitLast k)
      (Measure.pi fun _ : Fin (k+1) => μ) ((Measure.pi fun _ : Fin k => μ).prod μ) :=
  measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) (Fin.last k))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphere_iid_ae_independent (n : ℕ) (dim : n≤Module.finrank ℝ E) :
    ∀ᵐ (v : Fin n→UnitSphere E) ∂(Measure.pi fun _ : Fin n => uniformSphere (volume : Measure E)),
      LinearIndependent ℝ (fun i => (v i).val) := by
  let μ := uniformSphere (volume : Measure E)
  letI : IsProbabilityMeasure μ := uniformSphere_isProbability _
  induction n with
  | zero =>
    exact Filter.Eventually.of_forall (fun v => linearIndependent_empty_type)
  | succ k ih =>
    let e : (Fin (k+1)→UnitSphere E) ≃ᵐ ((Fin k→UnitSphere E)×UnitSphere E) := splitLast k
    let P : (Fin (k+1)→UnitSphere E) → Prop := fun v =>
      LinearIndependent ℝ (fun i => (v i).val)
    have le : k ≤ Module.finrank ℝ E := by omega
    have lt : k < Module.finrank ℝ E := by omega
    have hem : MeasurableSet {z | P (e.symm z)} :=
      measurableSet_anchor_independent.preimage e.symm.measurable
    have step : ∀ᵐ z ∂((Measure.pi fun _ : Fin k => μ).prod μ), P (e.symm z) := by
      apply (ae_prod_iff_ae_ae hem).mpr
      filter_upwards [ih le] with v hv
      filter_upwards [ae_anchor_extension v hv lt] with x hx
      dsimp only [P,e]
      rw [splitLast_symm_apply]
      have h : (fun i => (Fin.snoc (α:=fun _ => UnitSphere E) v x i).val) =
          Fin.snoc (fun i => (v i).val) x.val := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rwa [h]
    have pres := splitLast_volume μ k
    filter_upwards [pres.quasiMeasurePreserving.ae step] with v hv
    change P (e.symm (e v)) at hv
    simpa only [MeasurableEquiv.symm_apply_apply] using hv

#print axioms sphere_iid_ae_independent
end RobustFolkman.GeometricGap
