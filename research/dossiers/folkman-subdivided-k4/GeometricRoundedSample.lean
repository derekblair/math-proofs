import GeometricUniformRectangle
import GeometricBlockSampling
import GeometricDecoupledTail
import GeometricRowNorm

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable def centeredSample {J S : Type*} [DecidableEq J]
    (K : S→S→ℝ) (q : ℝ) (x : J→S) : Matrix J J ℝ :=
  Matrix.of fun i j => if i=j then 0 else K (x i) (x j)-q

/-- Concentration of the actual centered, square, finite-kernel sample.
No independence is assumed among entries of that matrix. -/
theorem rounded_sample_tail {D L : ℕ} (μ : Measure (Fin D)) [IsProbabilityMeasure μ]
    (K : Fin D→Fin D→ℝ) (sym : ∀ x y, K x y=K y x)
    (bin : ∀ x y, K x y=0 ∨ K x y=1) (q : ℝ) (qp : 0<q) (q1 : q≤1)
    (hD : 0<D) (Lq : 1≤(L:ℝ)*q)
    (row : ∀ y, μ.real {x | K x y=1}≤2*q)
    (features : ∀ x, ∑ j,(kernelFeature (fun x y => K x y-q) (fun z => (μ {z}).toReal) x j)^2≤3*q)
    (pop : ‖weightedKernel (fun x y => K x y-q) (fun z => (μ {z}).toReal)‖≤q/100) :
    let ν := Measure.pi (fun _ : Fin L => μ)
    ν.real {x | 3*(L:ℝ)*q/50<‖centeredSample K q x‖}
      ≤ ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) := by
  classical
  intro ν
  let T : Matrix (Fin L) (Fin L) ℝ →ₗ[ℝ] (EuclideanSpace ℝ (Fin L) →L[ℝ] EuclideanSpace ℝ (Fin L)) :=
    ((Matrix.toEuclideanLin (n:=Fin L) (m:=Fin L) (𝕜:=ℝ)).trans LinearMap.toContinuousLinearMap).toLinearMap
  let A := fun x : Fin L→Fin D => centeredSample K q x
  let g := (L:ℝ)*q/50
  let p := (2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000)
  have normT (M : Matrix (Fin L) (Fin L) ℝ) : ‖T M‖=‖M‖ :=
    (Matrix.l2_opNorm_def M).symm
  have diag (x : Fin L→Fin D) (i : Fin L) : A x i i=0 := by simp [A,centeredSample]
  have sa (x : Fin L→Fin D) (i j : Fin L) : A x i j=A x j i := by
    by_cases e : i=j
    · subst j; rfl
    · simp [A,centeredSample,e,Ne.symm e,sym]
  have size (x : Fin L→Fin D) (b : Fin L→Bool) : ‖T (crossPart (A x) b)‖≤(L:ℝ) := by
    rw [normT]
    apply symmetric_norm_le_row_sum _ (fun i j => by
      by_cases e : b i=b j
      · simp only [crossPart,ite_eq_right (not_not_intro e),ite_eq_right (not_not_intro e.symm)]
      · simp only [crossPart,ite_eq_left e,ite_eq_left (Ne.symm e),sa x i j]) _ (by positivity)
    intro i
    calc
      _ ≤ ∑ _ : Fin L, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases e : b i=b j
        · simp [crossPart,e]
        · have ne : i≠j := fun h => e (congrArg b h)
          simp only [crossPart,ite_eq_left e,A,centeredSample,Matrix.of_apply,ite_eq_right ne,Real.norm_eq_abs]
          rcases bin (x i) (x j) with h|h
          · rw [h,zero_sub,abs_neg,abs_of_nonneg qp.le]
            exact q1
          · rw [h,abs_of_nonneg (sub_nonneg.mpr q1)]
            linarith only [qp]
      _ = _ := by simp
  have det (x : Fin L→Fin D) (b : Fin L→Bool) :
      ‖crossRectangle (A x) b‖ =
        ‖crossBlock (fun x y => K x y-q) (blockSample b x).1 (blockSample b x).2‖ := by
    rw [←block_reindex_norm (A x) b]
    congr 1
    ext i j
    have hij : (leftReindex b i).val ≠ (rightReindex b j).val := by
      intro h
      exact (rightReindex b j).property (h ▸ (leftReindex b i).property)
    simp only [A,centeredSample,crossBlock,Matrix.of_apply,blockSample,ite_eq_right hij]
  have bad (b : Fin L→Bool) : ν.real {x | g<‖T (crossPart (A x) b)‖}≤p := by
    let n := Fintype.card (LeftBlock b)
    let m := Fintype.card (RightBlock b)
    let E := {z : (Fin n→Fin D)×(Fin m→Fin D) | g<‖crossBlock (fun x y => K x y-q) z.1 z.2‖}
    have em : MeasurableSet E := (Set.to_countable E).measurableSet
    have sub : {x | g<‖T (crossPart (A x) b)‖} ⊆ (blockSample b) ⁻¹' E := by
      intro x hx
      change g<‖T (crossPart (A x) b)‖ at hx
      rw [normT] at hx
      have z := cross_part_rectangular_norm (A x) (sa x) b
      rw [det] at z
      exact hx.trans_le z
    have h := ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (μ:=ν) sub)
    unfold Measure.real at h
    rw [(blockSample_preserving μ b).measure_preimage em.nullMeasurableSet] at h
    refine h.trans ?_
    by_cases hn : 0<n
    · have c := block_count_le b
      exact sample_rectangle_uniform μ K bin q qp q1 hn hD
        (c.1.trans_eq (Fintype.card_fin L)) (c.2.trans_eq (Fintype.card_fin L)) Lq row features pop
    · have z : n=0 := Nat.eq_zero_of_not_pos hn
      letI : IsEmpty (Fin n) := z ▸ Fin.isEmpty
      have d : E=∅ := by
        ext x
        have eq : crossBlock (fun x y => K x y-q) x.1 x.2=0 := by
          ext i j
          exact isEmptyElim i
        simp only [E,Set.mem_ofPred_eq,eq,norm_zero,Set.mem_empty_iff_false]
        exact iff_false_intro (not_lt_of_ge (by dsimp [g]; positivity))
      rw [d,measure_empty,ENNReal.toReal_zero]
      dsimp [p]
      positivity
  have h := decoupled_norm_tail ν T A diag g (L:ℝ) (q/100) p (by dsimp [g]; positivity)
    (by positivity) (by positivity) size (fun _ => (Set.to_countable _).measurableSet) bad
  have eq : 2*g+2*(L:ℝ)*(q/100)=3*(L:ℝ)*q/50 := by dsimp [g]; ring
  simpa only [eq,normT,A,p] using h

#print axioms rounded_sample_tail
end RobustFolkman.GeometricGap
