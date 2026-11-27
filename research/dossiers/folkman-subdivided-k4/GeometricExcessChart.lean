import GeometricTripleChart

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal Matrix

noncomputable def chartExcess (t : ℝ) (x : PairCoord (Fin 3)→ℝ) : ThreeReals :=
  tripleCoordinates (fun j => x j - t)

theorem chartExcess_volume (t : ℝ) : MeasurePreserving (chartExcess t) volume volume := by
  have h := measurePreserving_add_left (volume : Measure (PairCoord (Fin 3)→ℝ)) (fun _ => -t)
  convert tripleCoordinates_volume.comp h using 1
  funext x
  unfold chartExcess Function.comp
  congr 1
  funext j
  change x j - t = -t + x j
  ring

def excessGram (t : ℝ) (p : ThreeReals) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,t+p.1,t+p.2.1; t+p.1,1,t+p.2.2; t+p.2.1,t+p.2.2,1]

theorem excessGram_det (t : ℝ) (p : ThreeReals) :
    (excessGram t p).det = threeGramDet (t+p.1) (t+p.2.1) (t+p.2.2) := by
  rw [Matrix.det_fin_three]
  simp [excessGram,threeGramDet]
  ring

theorem chartExcess_gram (t : ℝ) (x : PairCoord (Fin 3)→ℝ) :
    excessGram t (chartExcess t x) = gramChart x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [excessGram,chartExcess,tripleCoordinates,triangleCoordOf,gramChart] <;> norm_num <;> ring

def triangleExcessRegion (t : ℝ) : Set ThreeReals :=
  {p | GramFeasible (fun i j => i≠j) t (excessGram t p)}

theorem triangleExcessRegion_measurable (t : ℝ) : MeasurableSet (triangleExcessRegion t) := by
  have h : Continuous (excessGram t) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp [excessGram] <;> fun_prop
  exact ((closed_gram_feasible (fun i j : Fin 3 => i≠j) t).preimage h).measurableSet

theorem triangleExcessRegion_within (t : ℝ) : triangleExcessRegion t ⊆ excessCube (1-t) := by
  intro p hp
  change GramFeasible (fun i j => i≠j) t (excessGram t p) at hp
  have upper (i j : Fin 3) : excessGram t p i j≤1 :=
    (abs_le.mp (abs_entry_le_one _ hp.1 hp.2.1 i j)).2
  have lower (i j : Fin 3) (ne : i≠j) : t≤excessGram t p i j := hp.2.2 i j ne
  have x := upper 0 1
  have y := upper 0 2
  have z := upper 1 2
  have xx := lower 0 1 (by decide)
  have yy := lower 0 2 (by decide)
  have zz := lower 1 2 (by decide)
  change t+p.1≤1 at x
  change t+p.2.1≤1 at y
  change t+p.2.2≤1 at z
  change t≤t+p.1 at xx
  change t≤t+p.2.1 at yy
  change t≤t+p.2.2 at zz
  exact ⟨⟨by linarith only [xx],by linarith only [x]⟩,
    ⟨by linarith only [yy],by linarith only [y]⟩,
    ⟨by linarith only [zz],by linarith only [z]⟩⟩

theorem triangleExcessRegion_inside (t w : ℝ) (t0 : 0≤t) (w0 : 0≤w)
    (small : 3*(t+w)<1) : excessCube w ⊆ triangleExcessRegion t := by
  intro p hp
  have hx := hp.1
  have hy := hp.2.1
  have hz := hp.2.2
  change 0≤p.1 ∧ p.1≤w at hx
  change 0≤p.2.1 ∧ p.2.1≤w at hy
  change 0≤p.2.2 ∧ p.2.2≤w at hz
  have sym : (excessGram t p).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [excessGram,Matrix.conjTranspose_apply]
  have pd : (excessGram t p).PosDef := by
    apply near_identity_pd _ sym (t+w) (by positivity) (by simpa [mul_comm] using small)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [excessGram] <;>
      first | positivity | (rw [abs_of_nonneg (by linarith only [t0,hx.1,hy.1,hz.1])]; linarith only [hx.2,hy.2,hz.2])
  refine ⟨pd.posSemidef,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i j ne
    fin_cases i <;> fin_cases j <;> first | contradiction | simp [excessGram,hx.1,hy.1,hz.1]

#print axioms triangleExcessRegion_inside
#print axioms triangleExcessRegion_within
end RobustFolkman.GeometricGap
