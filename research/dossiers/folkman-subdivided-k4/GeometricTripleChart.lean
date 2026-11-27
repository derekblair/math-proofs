import GeometricShellTail
import GeometricJointGramNormalized

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal

def triangleCoordOf (i : Fin 3) : PairCoord (Fin 3) :=
  if i=0 then ⟨(0,1),by decide⟩ else
  if i=1 then ⟨(0,2),by decide⟩ else ⟨(1,2),by decide⟩

theorem triangleCoordOf_inj : Function.Injective triangleCoordOf := by
  intro i j e
  fin_cases i <;> fin_cases j <;> first | rfl | exact (by decide : _ ≠ _) e | contradiction

theorem triangleCoordOf_surj : Function.Surjective triangleCoordOf := by
  rintro ⟨⟨i,j⟩,h⟩
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ ((0:Fin 3)<0)) h)
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact False.elim ((by decide : ¬ ((1:Fin 3)<0)) h)
  · exact False.elim ((by decide : ¬ ((1:Fin 3)<1)) h)
  · exact ⟨2,rfl⟩
  · exact False.elim ((by decide : ¬ ((2:Fin 3)<0)) h)
  · exact False.elim ((by decide : ¬ ((2:Fin 3)<1)) h)
  · exact False.elim ((by decide : ¬ ((2:Fin 3)<2)) h)

noncomputable def triangleCoordEquiv : Fin 3 ≃ PairCoord (Fin 3) :=
  Equiv.ofBijective triangleCoordOf ⟨triangleCoordOf_inj,triangleCoordOf_surj⟩

noncomputable def tripleCoordinates (x : PairCoord (Fin 3)→ℝ) : ThreeReals :=
  (x (triangleCoordOf 0), x (triangleCoordOf 1), x (triangleCoordOf 2))

theorem tripleCoordinates_volume :
    MeasurePreserving tripleCoordinates volume volume := by
  let F := MeasurableEquiv.piCongrLeft (fun _ : PairCoord (Fin 3) => ℝ) triangleCoordEquiv
  let G := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let H := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have f : MeasurePreserving F volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ => ℝ) triangleCoordEquiv
  -- F permutes chart coordinates in the direction Fin 3 → PairCoord.
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  have g := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have := h.comp (g.comp (f.symm F))
  convert this using 1
  rfl

theorem gramChart_three_det (x : PairCoord (Fin 3)→ℝ) :
    (gramChart x).det = threeGramDet (tripleCoordinates x).1
      (tripleCoordinates x).2.1 (tripleCoordinates x).2.2 := by
  rw [Matrix.det_fin_three]
  simp only [gramChart_diag,gramChart, tripleCoordinates, triangleCoordOf]
  norm_num
  unfold threeGramDet
  ring

#print axioms gramChart_three_det
#print axioms tripleCoordinates_volume
end RobustFolkman.GeometricGap
