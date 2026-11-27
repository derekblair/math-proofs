import GeometricCenteredCut
import GeometricCapKernel
import GeometricOperatorOrder
import GeometricSphereTransport

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory Set Finset WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {J E : Type*} [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem pointGraph_pair (t : ℝ) (x : J→UnitSphere E) {i j : J} (ne : i≠j) :
    ({i,j}:Finset J)∈pointGraph t x ↔ t≤⟪(x i).val,(x j).val⟫_ℝ := by
  classical
  unfold pointGraph
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨a,b⟩,⟨ab,h⟩,e⟩
    rcases pair_orientation ab e with ⟨ha,hb⟩|⟨ha,hb⟩
    · change a=i at ha; change b=j at hb; subst a; subst b; exact h
    · change a=j at ha; change b=i at hb; subst a; subst b; simpa only [real_inner_comm (x j).val (x i).val] using h
  · intro h
    exact ⟨(i,j),⟨ne,h⟩,rfl⟩

theorem pointGraph_edge_card2 (t : ℝ) (x : J→UnitSphere E) :
    ∀ e∈pointGraph t x, (e:Finset J).card=2 := by
  classical
  intro e he
  rcases Finset.mem_image.1 he with ⟨⟨i,j⟩,hi,rfl⟩
  exact card_pair (Finset.mem_filter.1 hi).2.1

theorem sample_graph_quadratic_of_norm (t q : ℝ) (x : J→UnitSphere E)
    (h : ‖linkAdjMatrix (pointGraph t x) - Matrix.of (fun _ _ : J => q)‖≤(Fintype.card J:ℝ)*q/10)
    (v : J→ℝ) :
    -(Fintype.card J:ℝ)*q/10*(∑ i,(v i)^2)≤v ⬝ᵥ
      ((linkAdjMatrix (pointGraph t x)-Matrix.of (fun _ _ : J => q)) *ᵥ v) := by
  let A := linkAdjMatrix (pointGraph t x) - Matrix.of (fun _ _ : J => q)
  let V : EuclideanSpace ℝ J := toLp 2 v
  have en : ‖V‖^2=∑ i, (v i)^2 := EuclideanSpace.real_norm_sq_eq V
  have eq : ⟪V,Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) A V⟫_ℝ = v ⬝ᵥ (A *ᵥ v) := Matrix.inner_toEuclideanCLM A V V
  have zz := abs_real_inner_le_norm V (Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) A V)
  have z := (Matrix.toEuclideanCLM (n:=J) (𝕜:=ℝ) A).le_opNorm V
  rw [Matrix.l2_opNorm_toEuclideanCLM] at z
  have p := mul_le_mul_of_nonneg_right h (norm_nonneg V)
  have f := mul_le_mul_of_nonneg_left (z.trans p) (norm_nonneg V)
  rw [eq] at zz
  have m : ‖V‖*((Fintype.card J:ℝ)*q/10*‖V‖)=(Fintype.card J:ℝ)*q/10*(∑ i, (v i)^2) := by
    rw [←en]
    ring
  rw [m] at f
  have bound := (abs_le.mp (zz.trans f)).1
  change -(Fintype.card J:ℝ)*q/10*(∑ i,(v i)^2)≤v ⬝ᵥ (A *ᵥ v)
  convert bound using 1 <;> ring

theorem sample_graph_cut_of_norm (t q : ℝ) (q0 : 0≤q) (x : J→UnitSphere E)
    (h : ‖linkAdjMatrix (pointGraph t x) - Matrix.of (fun _ _ : J => q)‖≤(Fintype.card J:ℝ)*q/10) :
    ∀ b : J→Bool, cutCount (pointGraph t x) b ≤ (9/16)*((pointGraph t x).card:ℝ) :=
  cuts_from_centered_quadratic _ q q0 (pointGraph_edge_card2 t x)
    (sample_graph_quadratic_of_norm t q x h)

theorem sample_graph_edge_lower_of_norm (t q : ℝ) (x : J→UnitSphere E)
    (h : ‖linkAdjMatrix (pointGraph t x) - Matrix.of (fun _ _ : J => q)‖≤(Fintype.card J:ℝ)*q/10) :
    (9/20)*(Fintype.card J:ℝ)^2*q ≤ ((pointGraph t x).card:ℝ) := by
  let n : ℝ := Fintype.card J
  let A := linkAdjMatrix (pointGraph t x)
  have b := sample_graph_quadratic_of_norm t q x h (fun _ => 1)
  change -n*q/10*(∑ _ : J,(1:ℝ)^2)≤(fun _ : J => (1:ℝ)) ⬝ᵥ ((A-Matrix.of (fun _ _ : J => q)) *ᵥ fun _ => 1) at b
  rw [Matrix.sub_mulVec,dotProduct_sub,constant_matrix_quadratic] at b
  simp only [one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,dotProduct,Matrix.mulVec,one_mul] at b
  change -n*q/10*n≤(∑ i,∑ j,A i j)-q*n^2 at b
  have e := directed_orient_count (pointGraph t x) (pointGraph_edge_card2 t x)
  change (∑ i,∑ j,A i j)=2*((pointGraph t x).card:ℝ) at e
  rw [e] at b
  change (9/20)*n^2*q≤_
  nlinarith only [b]

theorem measurable_pointGraph_pred (t : ℝ) (P : EdgeGraph J→Prop) :
    MeasurableSet {x : J→UnitSphere E | P (pointGraph t x)} := by
  classical
  have e : {x : J→UnitSphere E | P (pointGraph t x)} =
      ⋃ g ∈ (Finset.univ.filter P : Finset (EdgeGraph J)), fiberOf (pointGraph t) g := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h => ⟨pointGraph t x,h,rfl⟩,fun ⟨g,h,e⟩ => e.symm ▸ h⟩
  rw [e]
  exact MeasurableSet.biUnion (Finset.univ.filter P).countable_toSet (fun g _ => measurable_pointGraph_fiber t g)

#print axioms sample_graph_cut_of_norm
#print axioms sample_graph_edge_lower_of_norm
#print axioms measurable_pointGraph_pred
end RobustFolkman.GeometricGap
