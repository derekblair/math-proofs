import GeometricProjectionMass

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set
open scoped ENNReal

noncomputable def gramFiber (k m : ℕ)
    (f : (PairCoord (Fin (k+1))→ℝ)→ℝ≥0∞) (u : PairCoord (Fin k)→ℝ) : ℝ≥0∞ :=
  ∫⁻ y : Fin k→ℝ, chartWeight (k+1) m ((chartStep k).symm (u,y)) *
        f ((chartStep k).symm (u,y))

theorem gramFiber_measurable (k m : ℕ)
    (f : (PairCoord (Fin (k+1))→ℝ)→ℝ≥0∞) (fm : Measurable f) :
    Measurable (gramFiber k m f) :=
  (((chartWeight_measurable (k+1) m).mul fm).comp (chartStep k).symm.measurable).lintegral_prod_right'

theorem gramFiber_off_support (k m : ℕ)
    (f : (PairCoord (Fin (k+1))→ℝ)→ℝ≥0∞) (u : PairCoord (Fin k)→ℝ)
    (np : ¬(gramChart u).PosDef) :
    gramFiber k m f u=0 := by
  unfold gramFiber
  have z (y : Fin k→ℝ) : chartWeight (k+1) m ((chartStep k).symm (u,y))=0 := by
    let x := (chartStep k).symm (u,y)
    unfold chartWeight
    apply indicator_of_notMem
    intro h
    change (gramChart x).PosDef at h
    rw [gramChart_border_pd,(chartStep k).apply_symm_apply] at h
    apply np
    have p := h.submatrix (Sum.inl_injective : Function.Injective (Sum.inl : Fin k→Fin k⊕Unit))
    convert p using 1
    ext i j
    rfl
  simp [z]

theorem gramFiber_integrate (k m : ℕ)
    (f : (PairCoord (Fin (k+1))→ℝ)→ℝ≥0∞) (fm : Measurable f) :
    (∫⁻ u, gramFiber k m f u) = ∫⁻ x, chartWeight (k+1) m x * f x := by
  let G := fun x => chartWeight (k+1) m x * f x
  have Gm : Measurable G := (chartWeight_measurable _ _).mul fm
  have V := (chartStep_volume k).symm (chartStep k)
  have L := V.lintegral_comp Gm
  let H : ((PairCoord (Fin k)→ℝ)×(Fin k→ℝ))→ℝ≥0∞ :=
    fun z => G ((chartStep k).symm z)
  have Hm : Measurable H := Gm.comp (chartStep k).symm.measurable
  change (∫⁻ z, H z ∂((volume : Measure (PairCoord (Fin k)→ℝ)).prod volume)) = _ at L
  rw [lintegral_prod H Hm.aemeasurable] at L
  exact L

#print axioms gramFiber_integrate
end RobustFolkman.GeometricGap
