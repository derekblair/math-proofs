import GeometricRootedCount

namespace RobustFolkman.GeometricGap
open Finset MeasureTheory
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]

theorem rootedLink_mean (t : ℝ) (v : V) :
    Moment.mean (sphericalHostWeight (E:=E) t) (fun g => linkTriangleCount g v) =
      ((Fintype.card V-1).choose 2:ℝ) * (patternMass (E:=E) triangleCon t).toReal := by
  simp_rw [linkTriangleCount_indicator, Moment.mean_sum_of]
  calc
    _ = ∑ _ ∈ rootedTriples v, (patternMass (E:=E) triangleCon t).toReal := by
      apply Finset.sum_congr rfl
      intro s hs
      exact triangle_moment_exact t s (mem_powersetCard.mp (mem_filter.mp hs).1).2
    _ = _ := by simp [rootedTriples_card]

/-- The sharing-one-vertex independence leaves only the linear number
of two-vertex overlaps per rooted triangle in the variance. -/
theorem rootedLink_variance (t : ℝ) (v : V) :
    let u := (patternMass (E:=E) triangleCon t).toReal
    let q := (patternMass (E:=E) diamondEdges t).toReal
    let A : ℝ := (Fintype.card V-1).choose 2
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => (linkTriangleCount g v-A*u)^2) ≤ A*(u+(↑(3*(Fintype.card V-3)):ℝ)*q) := by
  classical
  intro u q A
  let p := sphericalHostWeight (V:=V) (E:=E) t
  let S := rootedTriples v
  let R := fun i j : Finset V => (j∩i).card=2
  have sc : ∀ s∈S, s.card=3 := fun s hs => (mem_powersetCard.mp (mem_filter.mp hs).1).2
  have m : ∀ i∈S, Moment.mean p (fun g => triangleIndicator g i) = u :=
    fun i hi => triangle_moment_exact t i (sc i hi)
  have q0 : 0≤q := ENNReal.toReal_nonneg
  have var := Moment.variance_indicator_upper p
    (sphericalHostWeight_probability (V:=V) (E:=E) t).2 S
    (fun i g => triangleIndicator g i) u q
    (fun i g => by unfold triangleIndicator; split <;> simp)
    m R
    (fun i j hi hj ne r => (nonedge_overlap_triangle_moments t i j (sc i hi) (sc j hj) ne r).le)
    (fun i j hi hj _ r => (diamond_moment_overlap_two t i j (sc i hi) (sc j hj) r).le)
  have row (i : Finset V) (hi : i∈S) :
      (((S.erase i).filter (R i)).card:ℝ) ≤ (↑(3*(Fintype.card V-3)):ℝ) := by
    have sub : ((S.erase i).filter (R i)) ⊆
        ((((univ : Finset V).powersetCard 3).erase i).filter (R i)) := by
      intro j hj
      obtain ⟨he, hr⟩ := mem_filter.mp hj
      obtain ⟨ne, hj⟩ := mem_erase.mp he
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨ne,(mem_filter.mp hj).1⟩,hr⟩
    apply Nat.cast_le.mpr
    exact (Finset.card_le_card sub).trans
      (by simpa only [card_univ] using Moment.triangle_overlap_row (univ : Finset V) i (mem_filter.mp hi).1)
  have rows : (∑ i∈S, (((S.erase i).filter (R i)).card:ℝ) * q)
      ≤ (S.card:ℝ)*((↑(3*(Fintype.card V-3)):ℝ)*q) := by
    calc
      _ ≤ ∑ _ ∈ S, (↑(3*(Fintype.card V-3)):ℝ)*q :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (row i hi) q0)
      _ = _ := by simp
  have hA : (S.card:ℝ)=A := by simp [S, A, rootedTriples_card]
  have final := var.trans (add_le_add_right rows ((S.card:ℝ)*u))
  rw [hA,←mul_add] at final
  simpa only [linkTriangleCount_indicator] using final

#print axioms rootedLink_mean
#print axioms rootedLink_variance
end RobustFolkman.GeometricGap
