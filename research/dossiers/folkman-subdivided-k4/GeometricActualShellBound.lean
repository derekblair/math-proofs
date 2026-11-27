import GeometricActualShell
import GeometricSpherePatternRate

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem sphere_triangle_excess_tail (m : ℕ) (dim : Module.finrank ℝ E=3+m+1)
    (t a b c : ℝ) (t0 : 0<t) (t1 : t≤1/8)
    (large : 36≤(m:ℝ)/2) (dense : 1≤((m:ℝ)/2)*t^2) :
    excessTriangleMass (E:=E) t
      (triangleExcessRegion t ∩ (Ici a ×ˢ (Ici b ×ˢ Ici c))) ≤
        ENNReal.ofReal (Real.exp (36-((m:ℝ)/2)*t*(a+b+c))) *
          excessTriangleMass (E:=E) t (triangleExcessRegion t) := by
  let G := triangleExcessRegion t
  let r := (m:ℝ)/2
  let Q := Ici a ×ˢ (Ici b ×ˢ Ici c)
  have rp : 0<r := by dsimp [r]; linarith only [large]
  have hm : 0<m := by exact_mod_cast (show (0:ℝ)<m by dsimp [r] at rp; linarith)
  have quarter : t≤1/4 := by linarith only [t1]
  have w0 : 0≤1/(r*t) := by positivity
  have w1 : 1/(r*t)≤t := by
    apply (div_le_iff₀ (mul_pos rp t0)).2
    change 1≤r*t^2 at dense
    nlinarith only [dense]
  have inside := triangleExcessRegion_inside t (1/(r*t)) t0.le w0
    (by linarith only [w1,t1])
  have bound := shell_orthant_mass_bound t r a b c t0 quarter large dense G inside
    (triangleExcessRegion_within t) (fun p hp => by
      rw [←excessGram_det]
      exact (show GramFeasible (fun i j => i≠j) t (excessGram t p) from hp).1.det_nonneg)
  have sm : MeasurableSet G := triangleExcessRegion_measurable t
  have qm : MeasurableSet Q := measurableSet_Ici.prod (measurableSet_Ici.prod measurableSet_Ici)
  obtain ⟨K,Klaw⟩ := exact_excess_triangle_measure (E:=E) m hm dim t t0.le quarter
  rw [Klaw (G ∩ Q) (sm.inter qm) inter_subset_left,Klaw G sm subset_rfl]
  calc
    _ ≤ K*(ENNReal.ofReal (Real.exp (36-r*t*(a+b+c))) * ∫⁻ p in G, shellWeight t r p) := by
      gcongr
    _ = _ := by dsimp only [r]; ac_rfl

theorem excessTriangleMass_all_edges (t : ℝ) :
    excessTriangleMass (E:=E) t (triangleExcessRegion t) =
      spherePatternMass (E:=E) (fun i j : Fin 3 => i≠j) t := by
  unfold excessTriangleMass spherePatternMass
  congr 1
  ext v
  change GramFeasible (fun i j => i≠j) t (excessGram t (chartExcess t (sampleChart v))) ↔
    GramFeasible (fun i j => i≠j) t (pointGram v)
  rw [chartExcess_gram,sampleChart_matrix]
  rfl

#print axioms sphere_triangle_excess_tail
#print axioms excessTriangleMass_all_edges
end RobustFolkman.GeometricGap
