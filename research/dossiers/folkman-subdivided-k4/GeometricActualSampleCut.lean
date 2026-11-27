import GeometricActualSampleNorm
import GeometricSampleCut

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator InnerProductSpace

theorem spherical_actual_cut_tail (n N : ℕ)
    [Nontrivial (EuclideanSpace ℝ (Fin (n+3)))]
    (t : ℝ) (tp : 0<t) (ts : t≤1/8) (a : GridSphere (n+3))
    (large : 3≤(n:ℝ)/2) (dense : 1≤4*((n:ℝ)/2)*t^2)
    (gap : Real.sqrt (squaredCapContraction n t)≤1/200) :
    let d := n+3
    let m := gridResolution n 20
    let σ := uniformSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))
    let q := σ.real (capPoints t a)
    let D := Fintype.card (GridCode d m)
    let L := N+1
    100≤(L:ℝ)*q →
    (Measure.pi (fun _ : Fin L => σ)).real {x |
      ∃ b : Fin L→Bool, (9/16)*((pointGraph t x).card:ℝ) < cutCount (pointGraph t x) b}
      ≤ ((2*(D:ℝ)+3*(L:ℝ))*Real.exp (-(L:ℝ)*q/1000000))/(q/100) +
        (L:ℝ)*Real.exp (-(L:ℝ)*q/1000) := by
  classical
  intro d m σ q D L Lq
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  let ν := Measure.pi (fun _ : Fin L => σ)
  have q0 : 0≤q := ENNReal.toReal_nonneg
  have q1 : q≤1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=σ) (s:=capPoints t a))
    exact h.trans_eq ENNReal.toReal_one
  have L100 : (100:ℝ)≤L := Lq.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left q1 (Nat.cast_nonneg L))
  have incl : {x : Fin L→GridSphere d |
      ∃ b : Fin L→Bool, (9/16)*((pointGraph t x).card:ℝ) < cutCount (pointGraph t x) b} ⊆
      {x | 4*(L:ℝ)*q/50<‖centeredSample (capKernel t) q x‖} := by
    intro x hx
    obtain ⟨b,hb⟩ := hx
    by_contra! bad
    have eq : linkAdjMatrix (pointGraph t x)-Matrix.of (fun _ _ : Fin L => q) =
        centeredSample (capKernel t) q x-q • (1 : Matrix (Fin L) (Fin L) ℝ) := by
      ext i j
      by_cases ij : i=j
      · subst j
        simp [linkAdjMatrix,centeredSample]
      · have a := pointGraph_pair t x ij
        simp [linkAdjMatrix,centeredSample,ij,a,capKernel_eq_ite]
    have norm : ‖linkAdjMatrix (pointGraph t x)-Matrix.of (fun _ _ : Fin L => q)‖≤
        (Fintype.card (Fin L):ℝ)*q/10 := by
      rw [eq,Fintype.card_fin]
      have p := norm_sub_le (centeredSample (capKernel t) q x) (q • (1:Matrix (Fin L) (Fin L) ℝ))
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg q0,norm_one,mul_one] at p
      have qq := mul_le_mul_of_nonneg_right L100 q0
      have bn : ‖centeredSample (capKernel t) q x‖≤4*(L:ℝ)*q/50 := le_of_not_gt bad
      linarith only [qq,p,bn,Lq]
    exact not_lt_of_ge (sample_graph_cut_of_norm t q q0 x norm b) hb
  exact (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (μ:=ν) incl)).trans
    (spherical_actual_sample_tail n N t tp ts a large dense gap Lq)

#print axioms spherical_actual_cut_tail
end RobustFolkman.GeometricGap
