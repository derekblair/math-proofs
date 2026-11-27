import GeometricSphereSampleTransfer

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped ENNReal BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {J E : Type*} [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem sample_graph_good_of_centeredSample (t q : ℝ) (q0 : 0≤q)
    (n : (100:ℝ)≤Fintype.card J) (x : J→UnitSphere E)
    (h : ‖centeredSample (capKernel t) q x‖≤4*(Fintype.card J:ℝ)*q/50) :
    (9/20:ℝ)*(Fintype.card J:ℝ)^2*q≤((pointGraph t x).card:ℝ) ∧
    (∀ b : J→Bool, cutCount (pointGraph t x) b≤(9/16)*((pointGraph t x).card:ℝ)) := by
  classical
  have np : 0<(Fintype.card J:ℝ) := (by norm_num : (0:ℝ)<100).trans_le n
  letI : Nonempty J := Fintype.card_pos_iff.1 (by exact_mod_cast np)
  have eq : linkAdjMatrix (pointGraph t x)-Matrix.of (fun _ _ : J => q) =
      centeredSample (capKernel t) q x-q • (1 : Matrix J J ℝ) := by
    ext i j
    by_cases ij : i=j
    · subst j
      simp [linkAdjMatrix,centeredSample]
    · have a := pointGraph_pair t x ij
      simp [linkAdjMatrix,centeredSample,ij,a,capKernel_eq_ite]
  have norm : ‖linkAdjMatrix (pointGraph t x)-Matrix.of (fun _ _ : J => q)‖≤
      (Fintype.card J:ℝ)*q/10 := by
    rw [eq]
    have p := norm_sub_le (centeredSample (capKernel t) q x) (q • (1:Matrix J J ℝ))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg q0,norm_one,mul_one] at p
    have qq := mul_le_mul_of_nonneg_right n q0
    have pp := mul_nonneg np.le q0
    linarith only [qq,p,h,pp]
  exact ⟨sample_graph_edge_lower_of_norm t q x norm,sample_graph_cut_of_norm t q q0 x norm⟩

#print axioms sample_graph_good_of_centeredSample
end RobustFolkman.GeometricGap
