import PlaneMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace PermCircles
open Set MeasureTheory Function

variable {I : Type*} [Fintype I]

lemma sqDist_shift (x a b : Point) : sqDist (x+a) b = sqDist x (b-a) := by
  simp [sqDist]
  ring

def cell (R : ℝ) (p : I → Point) (i : I) : Set Point :=
  {z | sqDist z (p i) ≤ R^2 ∧ ∀ j, sqDist z (p i) ≤ sqDist z (p j)}

def localCell (R : ℝ) (p : I → Point) (i : I) : Set Point :=
  {z | sqDist z 0 ≤ R^2 ∧ ∀ j, sqDist z 0 ≤ sqDist z (p j-p i)}

lemma cell_measurable (R : ℝ) (p : I → Point) (i : I) :
    MeasurableSet (cell R p i) := by
  have hM (j : I) : MeasurableSet {z | sqDist z (p i) ≤ sqDist z (p j)} :=
    measurableSet_le (continuous_sqDist _).measurable (continuous_sqDist _).measurable
  convert (disk_measurable R (p i)).inter (MeasurableSet.iInter hM) using 1
  ext z
  simp [cell,disk]

lemma localCell_eq_preimage (R : ℝ) (p : I → Point) (i : I) :
    localCell R p i = (fun z => z+p i) ⁻¹' cell R p i := by
  ext z
  change (sqDist z 0 ≤ R^2 ∧ ∀ j, sqDist z 0 ≤ sqDist z (p j-p i)) ↔
    (sqDist (z+p i) (p i) ≤ R^2 ∧ ∀ j, sqDist (z+p i) (p i) ≤ sqDist (z+p i) (p j))
  simp [sqDist_shift]

lemma volume_cell_translate (R : ℝ) (p : I → Point) (i : I) :
    volume (localCell R p i) = volume (cell R p i) := by
  rw [localCell_eq_preimage, measure_preimage_add_right]

lemma disk_cover_caps (R : ℝ) (p : I → Point) (i : I) :
    disk R 0 = localCell R p i ∪ ⋃ j, cap R (p j-p i) := by
  classical
  ext z
  change (sqDist z 0 ≤ R^2) ↔
    ((sqDist z 0 ≤ R^2 ∧ ∀ j, sqDist z 0 ≤ sqDist z (p j-p i)) ∨
      z ∈ ⋃ j, cap R (p j-p i))
  simp only [mem_iUnion]
  constructor
  · intro h
    by_cases hJ : ∀ j, sqDist z 0 ≤ sqDist z (p j-p i)
    · exact Or.inl ⟨h,hJ⟩
    · push_neg at hJ
      obtain ⟨j,hj⟩ := hJ
      exact Or.inr ⟨j,h,hj⟩
  · rintro (⟨h,_⟩|⟨j,h,_⟩) <;> exact h

lemma shadow_subdisk (R : ℝ) (b : Point) :
    shadow R b ⊆ disk R 0 := fun _ h => h.2.1

lemma self_shadow (R : ℝ) : shadow R (0 : Point) = ∅ := by
  ext z
  constructor
  · intro hz
    have hn := radial_sq R (show 0 < sqDist z 0 from hz.1)
    exact False.elim ((not_lt_of_ge (le_of_eq hn.symm)) hz.2.2)
  · simp

lemma sqDist_translated (a b d : Point) : sqDist (a-d) (b-d) = sqDist a b := by
  simp [sqDist]

lemma shadows_pairwise {r R : ℝ} (hR : R^2=4*r^2/3)
    (p : I → Point) (hp : ∀ i j, i ≠ j → 4*r^2 ≤ sqDist (p i) (p j))
    (i : I) : Pairwise (Disjoint on fun j => shadow R (p j-p i)) := by
  classical
  intro j k hjk
  change Disjoint (shadow R (p j-p i)) (shadow R (p k-p i))
  by_cases hj : j=i
  · subst j
    simp [self_shadow]
  by_cases hk : k=i
  · subst k
    simp [self_shadow]
  apply disjoint_left.2
  intro z h1 h2
  have ha : 4*r^2 ≤ sqDist 0 (p j-p i) := by
    rw [← sub_self (p i),sqDist_translated]
    exact hp i j (Ne.symm hj)
  have hb : 4*r^2 ≤ sqDist 0 (p k-p i) := by
    rw [← sub_self (p i),sqDist_translated]
    exact hp i k (Ne.symm hk)
  have hc : 4*r^2 ≤ sqDist (p j-p i) (p k-p i) := by
    rw [sqDist_translated]
    exact hp j k hjk
  exact shadows_separate hR ha hb hc h1 h2

#print axioms shadows_pairwise
end PermCircles
