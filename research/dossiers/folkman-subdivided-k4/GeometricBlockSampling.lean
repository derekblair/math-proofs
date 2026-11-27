import GeometricCrossOperator
import GeometricMatrixReindex
import GeometricConditionalRowTail

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {J S : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace S]

noncomputable def leftReindex (b : J→Bool) : Fin (Fintype.card (LeftBlock b)) ≃ LeftBlock b :=
  (Fintype.equivFin _).symm

noncomputable def rightReindex (b : J→Bool) : Fin (Fintype.card (RightBlock b)) ≃ RightBlock b :=
  (Fintype.equivFin _).symm

noncomputable def blockSample (b : J→Bool) (x : J→S) :
    (Fin (Fintype.card (LeftBlock b))→S)×(Fin (Fintype.card (RightBlock b))→S) :=
  (fun i => x (leftReindex b i).val, fun j => x (rightReindex b j).val)

theorem blockSample_preserving (σ : Measure S) [IsProbabilityMeasure σ] (b : J→Bool) :
    MeasurePreserving (blockSample (S:=S) b) (Measure.pi (fun _ : J => σ))
    ((Measure.pi (fun _ : Fin (Fintype.card (LeftBlock b)) => σ)).prod
      (Measure.pi (fun _ : Fin (Fintype.card (RightBlock b)) => σ))) := by
  have a := measurePreserving_piEquivPiSubtypeProd (fun _ : J => σ) (fun i => b i=false)
  have l := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card (LeftBlock b)) => σ) (leftReindex b).symm
  have r := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card (RightBlock b)) => σ) (rightReindex b).symm
  convert (l.prod r).comp a using 1
  funext x
  apply Prod.ext
  · funext i
    let X := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => S) (fun i => b i=false)) x
    change x (leftReindex b i).val =
      MeasurableEquiv.piCongrLeft (fun _ => S) (leftReindex b).symm X.1 i
    have h := MeasurableEquiv.piCongrLeft_apply_apply (leftReindex b).symm (β:=fun _ => S) X.1 (leftReindex b i)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  · funext i
    let X := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => S) (fun i => b i=false)) x
    change x (rightReindex b i).val =
      MeasurableEquiv.piCongrLeft (fun _ => S) (rightReindex b).symm X.2 i
    have h := MeasurableEquiv.piCongrLeft_apply_apply (rightReindex b).symm (β:=fun _ => S) X.2 (rightReindex b i)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm

theorem block_reindex_norm (A : Matrix J J ℝ) (b : J→Bool) :
    ‖(Matrix.of fun (i : Fin (Fintype.card (LeftBlock b))) (j : Fin (Fintype.card (RightBlock b))) =>
      A (leftReindex b i).val (rightReindex b j).val : Matrix _ _ ℝ)‖=‖crossRectangle A b‖ :=
  rectangular_reindex_norm (crossRectangle A b) (leftReindex b) (rightReindex b)

theorem block_count_le (b : J→Bool) :
    Fintype.card (LeftBlock b) ≤ Fintype.card J ∧ Fintype.card (RightBlock b) ≤ Fintype.card J :=
  ⟨Fintype.card_le_of_injective Subtype.val Subtype.val_injective,
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective⟩

#print axioms blockSample_preserving
#print axioms block_reindex_norm
end RobustFolkman.GeometricGap
