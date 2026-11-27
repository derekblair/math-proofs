import GeometricRoundedSample
import GeometricMatrixReindex

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset
open scoped ENNReal BigOperators Matrix.Norms.L2Operator
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem rounded_finite_tail {L : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω→Ω→ℝ) (sym : ∀ x y, K x y=K y x)
    (bin : ∀ x y, K x y=0 ∨ K x y=1) (q : ℝ) (qp : 0<q) (q1 : q≤1)
    (Lq : 1≤(L:ℝ)*q)
    (row : ∀ y, μ.real {x | K x y=1}≤2*q)
    (feat : ∀ x, ∑ j,(kernelFeature (fun x y => K x y-q) (fun z => (μ {z}).toReal) x j)^2≤3*q)
    (pop : ‖weightedKernel (fun x y => K x y-q) (fun z => (μ {z}).toReal)‖≤q/100) :
    let ν := Measure.pi (fun _ : Fin L => μ)
    ν.real {x | 3*(L:ℝ)*q/50<‖centeredSample K q x‖}
      ≤ ((2*(Fintype.card Ω:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) := by
  intro ν
  let D := Fintype.card Ω
  let e : Ω ≃ Fin D := Fintype.equivFin Ω
  let E : Ω ≃ᵐ Fin D := ⟨e,measurable_of_finite _,measurable_of_finite _⟩
  let τ := Measure.map E μ
  letI : IsProbabilityMeasure τ := by
    constructor
    rw [Measure.map_apply E.measurable MeasurableSet.univ]
    simp
  have hD : 0<D := @Fintype.card_pos Ω _ (nonempty_of_isProbabilityMeasure μ)
  have P : MeasurePreserving E μ τ := ⟨E.measurable,rfl⟩
  have law := measurePreserving_pi (fun _ : Fin L => μ) (fun _ => τ) (fun _ => P)
  let G := fun i j : Fin D => K (e.symm i) (e.symm j)
  have atom (i : Fin D) : τ {i}=μ {e.symm i} := by
    unfold τ
    rw [Measure.map_apply E.measurable (measurableSet_singleton i)]
    congr 1
    ext x
    change e x∈({i}:Set (Fin D)) ↔ x∈({e.symm i}:Set Ω)
    simp only [mem_singleton_iff]
    exact e.eq_symm_apply.symm
  have r (j : Fin D) : τ.real {i | G i j=1}≤2*q := by
    unfold τ Measure.real
    rw [Measure.map_apply E.measurable (Set.to_countable _).measurableSet]
    have z : E ⁻¹' {i | G i j=1}={x | K x (e.symm j)=1} := by
      ext x
      change K (e.symm (e x)) (e.symm j)=1 ↔ K x (e.symm j)=1
      rw [e.symm_apply_apply]
    rw [z]
    exact row _
  have f (i : Fin D) : ∑ j,(kernelFeature (fun x y => G x y-q) (fun z => (τ {z}).toReal) i j)^2≤3*q := by
    simp_rw [kernelFeature,atom]
    change ∑ j, ((K (e.symm i) (e.symm j)-q)*Real.sqrt ((μ {e.symm j}).toReal))^2≤_
    rw [e.symm.sum_comp (fun j => ((K (e.symm i) j-q)*Real.sqrt ((μ {j}).toReal))^2)]
    exact feat (e.symm i)
  have gg : weightedKernel (fun x y => G x y-q) (fun z => (τ {z}).toReal) =
      (weightedKernel (fun x y => K x y-q) (fun z => (μ {z}).toReal)).submatrix e.symm e.symm := by
    ext i j
    simp [weightedKernel,kernelFeature,Matrix.submatrix_apply,atom,G]
  have pp : ‖weightedKernel (fun x y => G x y-q) (fun z => (τ {z}).toReal)‖≤q/100 := by
    rw [gg,rectangular_reindex_norm]
    exact pop
  let B := {y : Fin L→Fin D | 3*(L:ℝ)*q/50<‖centeredSample G q y‖}
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have h := rounded_sample_tail τ G (fun i j => sym _ _) (fun i j => bin _ _) q qp q1 hD Lq r f pp
  have pre : (fun x : Fin L→Ω => fun i => E (x i)) ⁻¹' B =
    {x : Fin L→Ω | 3*(L:ℝ)*q/50<‖centeredSample K q x‖} := by
    have eq (x : Fin L→Ω) : centeredSample G q (fun i => E (x i))=centeredSample K q x := by
      ext i j
      change (if i=j then 0 else K (e.symm (e (x i))) (e.symm (e (x j)))-q) =
        (if i=j then 0 else K (x i) (x j)-q)
      rw [e.symm_apply_apply,e.symm_apply_apply]
    ext x
    simp only [B,Set.mem_preimage,mem_ofPred_eq,eq]
  unfold Measure.real
  rw [←pre,law.measure_preimage hB.nullMeasurableSet]
  exact h

#print axioms rounded_finite_tail
end RobustFolkman.GeometricGap
