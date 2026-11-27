import GeometricRowNorm
import GeometricQuantizedCap
import GeometricConditionalRowTail

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Matrix Finset WithLp
open scoped InnerProductSpace ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable def sampleCapError {d m N : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (t : ℝ) (a : GridSphere d) (x : Fin N → GridSphere d) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i=j then 0 else
    quantizedCapKernel t a (gridCode d m (x i)) (gridCode d m (x j))-capKernel t (x i) (x j)

theorem sample_cap_error_row {d m N : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (mp : 0<m) (t : ℝ) (a : GridSphere d) (x : Fin (N+1)→GridSphere d) (i : Fin (N+1)) :
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    let E := pairHeightStrip (E:=EuclideanSpace ℝ (Fin d)) (t-δ) (t+δ)
    ∑ j, ‖sampleCapError (m:=m) t a x i j‖ ≤
      ((retained ((fun b => (x i,b)) ⁻¹' E) (fun j : Fin N => x (i.succAbove j))).card:ℝ) := by
  classical
  intro δ E
  rw [i.sum_univ_succAbove]
  have dd : sampleCapError (m:=m) t a x i i=0 := by unfold sampleCapError; simp
  rw [dd,norm_zero,zero_add]
  unfold sampleCapError
  let U := fun j : Fin N => E.indicator (fun _ => (1:ℝ)) (x i,x (i.succAbove j))
  have le : (∑ j : Fin N, ‖if i=i.succAbove j then (0:ℝ) else
        quantizedCapKernel t a (gridCode d m (x i)) (gridCode d m (x (i.succAbove j)))-
          capKernel t (x i) (x (i.succAbove j))‖) ≤ ∑ j, U j := by
    apply Finset.sum_le_sum
    intro j _
    rw [ite_eq_right (i.succAbove_ne j).symm]
    exact quantized_cap_strip mp t a (x i,x (i.succAbove j))
  refine le.trans_eq ?_
  simp only [U,Set.indicator]
  rw [←Finset.sum_filter]
  simp [retained]

/-- The empirical Chebyshev-free transfer from the geometric grid costs a
strip-degree event. No independence is assumed between different rows. -/
theorem sample_cap_quantization_tail (n m N k : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (mp : 0<m) (t : ℝ) (a : GridSphere (n+3))
    (lo : -1≤t-2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ)))
    (hi : t+2*(Real.sqrt ((n+3:ℕ):ℝ)/(m:ℝ))≤1) :
    let d := n+3
    let δ := 2*(Real.sqrt (d:ℝ)/(m:ℝ))
    let Z := (sliceMass ((n:ℝ)/2) (-1) 1).toReal
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (Measure.pi (fun _ : Fin (N+1) => σ))
        {x | (k:ℝ)<‖sampleCapError (m:=m) t a x‖} ≤
      (N+1:ℝ≥0∞)*ENNReal.ofReal (Real.exp (2*(N:ℝ)*(2*δ/Z))/(2:ℝ)^k) := by
  classical
  intro d δ Z σ
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let E := pairHeightStrip (E:=EuclideanSpace ℝ (Fin d)) (t-δ) (t+δ)
  let B := fun i : Fin (N+1) => {x : Fin (N+1)→GridSphere d |
    k≤(retained ((fun b => (x i,b)) ⁻¹' E) (fun j : Fin N => x (i.succAbove j))).card}
  let μ := Measure.pi (fun _ : Fin (N+1) => σ)
  have each (a' : GridSphere d) : σ.real ((fun b => (a',b)) ⁻¹' E) ≤ 2*δ/Z := by
    have fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d))=n+3 := by simp [d]
    have δ0 : 0≤δ := by dsimp [δ]; positivity
    have h := root_strip_real_bound n fin a' (t-δ) (t+δ) lo hi (by linarith only [δ0])
    change σ.real ((fun b => (a',b)) ⁻¹' E) ≤ (t+δ-(t-δ))/Z at h
    rwa [show t+δ-(t-δ)=2*δ by ring] at h
  have incl : {x | (k:ℝ)<‖sampleCapError (m:=m) t a x‖} ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin (N+1))), B i := by
    intro x hx
    change (k:ℝ)<‖sampleCapError (m:=m) t a x‖ at hx
    by_contra notU
    apply (not_le_of_gt hx)
    refine symmetric_norm_le_row_sum _ ?_ (k:ℝ) (by positivity) ?_
    · intro i j
      by_cases e : i=j
      · subst j; rfl
      · unfold sampleCapError
        rw [ite_eq_right e,ite_eq_right (Ne.symm e)]
        unfold quantizedCapKernel
        rw [capKernel_symm t (x i),capKernel_symm t (cellRepresentative a (gridCode d m (x i)))]
    · intro i
      have abs : x∉B i := fun ab =>
        notU (Set.mem_iUnion.2 ⟨i,Set.mem_iUnion.2 ⟨Finset.mem_univ _,ab⟩⟩)
      have lim := Nat.le_of_lt (Nat.lt_of_not_ge abs)
      have h := sample_cap_error_row mp t a x i
      change (∑ j, ‖sampleCapError (m:=m) t a x i j‖) ≤
        ((retained ((fun b => (x i,b)) ⁻¹' E) (fun j : Fin N => x (i.succAbove j))).card:ℝ) at h
      exact h.trans (by exact_mod_cast lim)
  calc
    _ ≤ μ (⋃ i ∈ (Finset.univ : Finset (Fin (N+1))), B i) := measure_mono incl
    _ ≤ ∑ i : Fin (N+1), μ (B i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i : Fin (N+1), ENNReal.ofReal (Real.exp (2*(N:ℝ)*(2*δ/Z))/(2:ℝ)^k) :=
      Finset.sum_le_sum fun i _ => fixed_sample_row_tail σ E
        (pairHeightStrip_measurable _ _) (2*δ/Z) each N k i
    _ = _ := by simp [nsmul_eq_mul,Nat.cast_add]

#print axioms sample_cap_quantization_tail
end RobustFolkman.GeometricGap
