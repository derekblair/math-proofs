import GeometricCrossBernstein
import GeometricTrimmedColumns

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset RMT
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable def crossBlock {D n m : ℕ} (K : Fin D→Fin D→ℝ)
    (x : Fin n→Fin D) (y : Fin m→Fin D) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i j => K (x i) (y j)

/-- Two independent samples of the same finite kernel. The dependence
between entries is handled by two conditional covariance estimates. -/
theorem sample_rectangle_tail {D n m k : ℕ} (μ : Measure (Fin D))
    [IsProbabilityMeasure μ] (K : Fin D→Fin D→ℝ)
    (bin : ∀ x y, K x y=0 ∨ K x y=1)
    (q p A ρ s u : ℝ) (q0 : 0≤q) (A0 : 0<A) (ρ0 : 0≤ρ) (sp : 0<s) (up : 0<u)
    (hd : 0<D) (hn : 0<n) (B0 : 0<(n:ℝ)*q^2+(k:ℝ))
    (row : ∀ y, μ.real {x | K x y=1}≤p)
    (features : ∀ x, ∑ j,(kernelFeature (fun x y => K x y-q) (fun z => (μ {z}).toReal) x j)^2≤A)
    (pop : ‖weightedKernel (fun x y => K x y-q) (fun z => (μ {z}).toReal)‖≤ρ) :
    let ν := Measure.pi (fun _ : Fin n => μ)
    let τ := Measure.pi (fun _ : Fin m => μ)
    let T := (n:ℝ)*ρ^2+s
    let B := (n:ℝ)*q^2+(k:ℝ)
    (ν.prod τ) {z : (Fin n→Fin D)×(Fin m→Fin D) |
      Real.sqrt ((m:ℝ)*T+u)<‖crossBlock (fun x y => K x y-q) z.1 z.2‖} ≤
      ENNReal.ofReal (matrixBernsteinTailBound D ((n:ℝ)*A*ρ^2) (A+ρ^2) s) +
      ENNReal.ofReal (matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) u) +
      (m:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*(n:ℝ)*p)/(2:ℝ)^k) := by
  classical
  intro ν τ T B
  let L := fun x y => K x y-q
  let w := fun z : Fin D => (μ {z}).toReal
  let M := weightedMatrix w (fun x => rankOneMat (kernelFeature L w x))
  let V := fun x : Fin n→Fin D => ∑ i,rankOneMat (kernelFeature L w (x i))
  let S := {x : Fin n→Fin D | s≤‖V x-(n:ℝ) • M‖}
  let good := fun x : Fin n→Fin D => fun y : Fin D =>
    decide (∑ i,(rightColumn L x y i)^2≤B)
  let R := {z : (Fin n→Fin D)×(Fin m→Fin D) | z.1∉S ∧
    Real.sqrt ((m:ℝ)*T+u)<‖truncatedCross L z.1 (good z.1) z.2‖}
  let C := {z : (Fin n→Fin D)×(Fin m→Fin D) | ∃ j : Fin m,
    B<∑ i,(rightColumn L z.1 (z.2 j) i)^2}
  have Rm : MeasurableSet R := (Set.to_countable R).measurableSet
  have leftBound : ν S ≤ ENNReal.ofReal (matrixBernsteinTailBound D ((n:ℝ)*A*ρ^2) (A+ρ^2) s) := by
    have h := iid_feature_covariance_tail (N:=n) μ L A ρ s A0 ρ0 sp hd features pop
    change (ν S).toReal ≤ _ at h
    have hl := ENNReal.ofReal_le_ofReal h
    rwa [ENNReal.ofReal_toReal (measure_ne_top ν _)] at hl
  have RBound : (ν.prod τ) R ≤ ENNReal.ofReal (matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) u) := by
    rw [Measure.prod_apply Rm]
    calc
      _ ≤ ∫⁻ _ : Fin n→Fin D, ENNReal.ofReal
          (matrixBernsteinTailBound n ((m:ℝ)*B*T) (B+T) u) ∂ν := by
        apply lintegral_mono
        intro x
        change τ (Prod.mk x ⁻¹' R) ≤ _
        by_cases hx : x∈S
        · have z : Prod.mk x ⁻¹' R=∅ := by
            ext y
            simp [R,hx]
          rw [z,measure_empty]
          exact bot_le
        · have z : Prod.mk x ⁻¹' R =
              {y | Real.sqrt ((m:ℝ)*T+u)<‖truncatedCross L x (good x) y‖} := by
            ext y
            simp [R,hx]
          rw [z]
          have sumBound : ‖V x‖≤T := by
            have hm : ‖M‖≤ρ^2 := by
              unfold M
              rw [kernel_feature_population_norm L w (fun _ => ENNReal.toReal_nonneg)]
              exact pow_le_pow_left₀ (norm_nonneg _) pop 2
            have v : ‖V x‖≤‖V x-(n:ℝ) • M‖+‖(n:ℝ) • M‖ := norm_le_norm_sub_add _ _
            rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤n)] at v
            have sx : ‖V x-(n:ℝ) • M‖<s := lt_of_not_ge hx
            have mm := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n)
            dsimp [T]
            linarith only [sx,mm,v]
          have r := iid_truncated_cross_tail (k:=m) μ L x (good x) B T u B0 (by dsimp [T]; positivity)
            up hn (fun y hy => of_decide_eq_true hy) sumBound
          have r' := ENNReal.ofReal_le_ofReal r
          rwa [ENNReal.ofReal_toReal (measure_ne_top τ _)] at r'
      _ = _ := by rw [lintegral_const,measure_univ,mul_one]
  have cb : (ν.prod τ) C ≤ _ := all_column_energy_tail μ K bin q p q0 row n m k
  have inc : {z : (Fin n→Fin D)×(Fin m→Fin D) |
      Real.sqrt ((m:ℝ)*T+u)<‖crossBlock L z.1 z.2‖} ⊆
      ((S ×ˢ Set.univ) ∪ R) ∪ C := by
    intro z hz
    by_cases a : z∈C
    · exact Or.inr a
    · apply Or.inl
      by_cases hx : z.1∈S
      · exact Or.inl ⟨hx,Set.mem_univ _⟩
      · apply Or.inr
        refine ⟨hx,?_⟩
        have eq : truncatedCross L z.1 (good z.1) z.2=crossBlock L z.1 z.2 := by
          ext i j
          have ne : ¬B<∑ i,(rightColumn L z.1 (z.2 j) i)^2 := fun h => a ⟨j,h⟩
          have gj : good z.1 (z.2 j)=true := decide_eq_true (le_of_not_gt ne)
          simp only [truncatedCross,Matrix.of_apply,crossBlock,gj,ite_true,rightColumn]
        rwa [eq]
  calc
    _ ≤ (ν.prod τ) (((S ×ˢ Set.univ) ∪ R) ∪ C) := measure_mono inc
    _ ≤ (ν.prod τ) ((S ×ˢ Set.univ) ∪ R)+(ν.prod τ) C := measure_union_le _ _
    _ ≤ ((ν.prod τ) (S ×ˢ Set.univ)+(ν.prod τ) R)+(ν.prod τ) C :=
      add_le_add_left (measure_union_le _ _) _
    _ ≤ _ := by
      rw [Measure.prod_prod,measure_univ,mul_one]
      exact add_le_add (add_le_add leftBound RBound) cb

#print axioms sample_rectangle_tail
end RobustFolkman.GeometricGap
