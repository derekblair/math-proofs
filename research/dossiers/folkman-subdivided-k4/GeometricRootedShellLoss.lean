import GeometricRootedExcess
import GeometricShellLoss

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def lostRootTriangle (t w : ℝ) (a : UnitSphere E) : Set (UnitSphere E×UnitSphere E) :=
  triangleAt t a ∩ {p | t+w≤⟪a.val,p.1.val⟫_ℝ ∨ t+w≤⟪a.val,p.2.val⟫_ℝ}

theorem fixedRootExcess_triangle (t : ℝ) (a : UnitSphere E) :
    fixedRootExcess t a ⁻¹' triangleExcessRegion t = triangleAt t a := by
  ext p
  let u : Fin 3 → UnitSphere E := ![a,p.1,p.2]
  have h : fixedRootExcess t a p=chartExcess t (sampleChart u) := rfl
  change GramFeasible (fun i j=>i≠j) t (excessGram t (fixedRootExcess t a p)) ↔ p∈triangleAt t a
  rw [h,chartExcess_gram,sampleChart_matrix]
  change GramFeasible (fun i j=>i≠j) t (pointGram u) ↔ _
  constructor
  · intro g
    exact ⟨g.2.2 0 1 (by decide),g.2.2 0 2 (by decide),g.2.2 1 2 (by decide)⟩
  · rintro ⟨b,c,d⟩
    refine ⟨Matrix.posSemidef_gram ℝ _,pointGram_diag _,?_⟩
    intro i j ij
    fin_cases i <;> fin_cases j
    all_goals first | contradiction | exact b | exact c | exact d |
      solve | change t≤⟪p.1.val,a.val⟫_ℝ; rwa [real_inner_comm]
            | change t≤⟪p.2.val,a.val⟫_ℝ; rwa [real_inner_comm]
            | change t≤⟪p.2.val,p.1.val⟫_ℝ; rwa [real_inner_comm]

theorem fixedRootExcess_lost (t w : ℝ) (a : UnitSphere E) :
    (fixedRootExcess t a ⁻¹' (triangleExcessRegion t ∩ {p | w≤p.1 ∨ w≤p.2.1})) =
      lostRootTriangle t w a := by
  rw [Set.preimage_inter,fixedRootExcess_triangle]
  unfold lostRootTriangle
  congr 1
  ext p
  change (w≤⟪a.val,p.1.val⟫_ℝ-t ∨ w≤⟪a.val,p.2.val⟫_ℝ-t) ↔
    (t+w≤⟪a.val,p.1.val⟫_ℝ ∨ t+w≤⟪a.val,p.2.val⟫_ℝ)
  have A : w≤⟪a.val,p.1.val⟫_ℝ-t ↔ t+w≤⟪a.val,p.1.val⟫_ℝ := by constructor <;> intro h <;> linarith only [h]
  have B : w≤⟪a.val,p.2.val⟫_ℝ-t ↔ t+w≤⟪a.val,p.2.val⟫_ℝ := by constructor <;> intro h <;> linarith only [h]
  rw [A,B]

theorem fixed_root_shell_loss (m : ℕ) (dim : Module.finrank ℝ E=3+m+1)
    (t A : ℝ) (t0 : 0<t) (t1 : t≤1/8)
    (large : 36≤(m:ℝ)/2) (dense : 1≤((m:ℝ)/2)*t^2) (a : UnitSphere E) :
    let σ := uniformSphere (volume : Measure E)
    let w := A/(((m:ℝ)/2)*t)
    (σ.prod σ) (lostRootTriangle t w a) ≤
      (2*ENNReal.ofReal (Real.exp (36-A))) * (σ.prod σ) (triangleAt t a) := by
  intro σ w
  have h := triangle_shell_lost_mass (E:=E) m dim t A t0 t1 large dense
  have s := triangleExcessRegion_measurable t
  have U : MeasurableSet {p : ThreeReals | w≤p.1 ∨ w≤p.2.1} := by
    exact (measurableSet_le measurable_const measurable_fst).union
      (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))
  have r := fixedRootExcess_mass t a _ (s.inter U)
  have g := fixedRootExcess_mass t a _ s
  rw [fixedRootExcess_lost] at r
  rw [fixedRootExcess_triangle] at g
  rwa [r,g]

#print axioms fixed_root_shell_loss
end RobustFolkman.GeometricGap
