import GeometricStrictGram
import GeometricLaplaceBounds

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [LinearOrder I]

abbrev PairCoord (I : Type*) [LT I] := {p : I×I // p.1 < p.2}

noncomputable def gramChart (x : PairCoord I→ℝ) : Matrix I I ℝ :=
  fun i j => if h : i < j then x ⟨(i,j),h⟩ else
    if h' : j < i then x ⟨(j,i),h'⟩ else 1

theorem gramChart_diag (x : PairCoord I→ℝ) (i : I) : gramChart x i i=1 := by
  simp [gramChart]

theorem gramChart_symmetric (x : PairCoord I→ℝ) (i j : I) : gramChart x i j=gramChart x j i := by
  by_cases h : i < j
  · simp [gramChart,h,not_lt_of_ge h.le]
  · by_cases k : j < i
    · simp [gramChart,k,h]
    · simp [gramChart,k,h]

theorem gramChart_hermitian (x : PairCoord I→ℝ) : (gramChart x).IsHermitian := by
  ext i j
  simpa [Matrix.conjTranspose_apply] using gramChart_symmetric x j i

theorem gramChart_continuous : Continuous (gramChart (I:=I)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold gramChart
  split
  · rename_i h
    exact continuous_apply (⟨(i,j),h⟩ : PairCoord I)
  · split
    · rename_i h
      exact continuous_apply (⟨(j,i),h⟩ : PairCoord I)
    · exact continuous_const

theorem gramChart_surjective_on_correlation (M : Matrix I I ℝ)
    (sym : M.IsHermitian) (diag : ∀ i, M i i=1) :
    gramChart (fun p : PairCoord I => M p.val.1 p.val.2)=M := by
  ext i j
  by_cases h : i < j
  · simp [gramChart,h]
  · by_cases k : j < i
    · have e := congrFun (congrFun sym.eq i) j
      have e' : M j i=M i j := by simpa [Matrix.conjTranspose_apply] using e
      simpa [gramChart,h,k] using e'
    · have z : i=j := le_antisymm (le_of_not_gt k) (le_of_not_gt h)
      subst j
      simp [gramChart,diag]


theorem gram_open_inner (C : I→I→Prop) (t k : ℝ)
    (n : Fintype.card I≤6) (Q : Matrix I I ℝ)
    (sym : Q.IsHermitian) (diag : ∀ i, Q i i=1)
    (edges : ∀ i j, C i j → t<Q i j)
    (close : ∀ i j, |Q i j-(1:Matrix I I ℝ) i j|<1/8)
    (d : k<Q.det) :
    ∃ U : Set (PairCoord I→ℝ), IsOpen U ∧ U.Nonempty ∧
      ∀ x∈U, GramFeasible C t (gramChart x) ∧ k<(gramChart x).det := by
  let F i j : Set (PairCoord I→ℝ) := {x | |gramChart x i j-(1:Matrix I I ℝ) i j|<1/8}
  let L i j : Set (PairCoord I→ℝ) := {x | C i j → t<gramChart x i j}
  let D : Set (PairCoord I→ℝ) := {x | k<(gramChart x).det}
  let U := ((⋂ i, ⋂ j, F i j) ∩ (⋂ i, ⋂ j, L i j)) ∩ D
  have ev (i j : I) : Continuous (fun x : PairCoord I→ℝ => gramChart x i j) :=
    ((continuous_apply j).comp (continuous_apply i)).comp gramChart_continuous
  have f (i j : I) : IsOpen (F i j) :=
    isOpen_lt ((ev i j).sub continuous_const).abs continuous_const
  have l (i j : I) : IsOpen (L i j) := by
    by_cases h : C i j
    · simpa [L,h] using isOpen_lt (continuous_const (y:=t)) (ev i j)
    · simp [L,h]
  have dd : IsOpen D := isOpen_lt continuous_const (gram_det_continuous.comp gramChart_continuous)
  have uu : IsOpen U := ((isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite (f i)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite (l i))).inter dd
  let y : PairCoord I→ℝ := fun p => Q p.val.1 p.val.2
  have ey : gramChart y=Q := gramChart_surjective_on_correlation Q sym diag
  have yn : y∈U := by
    simp only [U,F,L,D,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq,ey]
    exact ⟨⟨close,edges⟩,d⟩
  refine ⟨U,uu,⟨y,yn⟩,?_⟩
  intro x hx
  simp only [U,F,L,D,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq] at hx
  have nc : (Fintype.card I:ℝ)≤6 := by exact_mod_cast n
  have pos := near_identity_pd (gramChart x) (gramChart_hermitian x) (1/8)
    (by norm_num) (by linarith only [nc]) (fun i j => (hx.1.1 i j).le)
  exact ⟨⟨pos.posSemidef,gramChart_diag x,fun i j h => (hx.1.2 i j h).le⟩,hx.2⟩

#print axioms gram_open_inner
end RobustFolkman.GeometricGap
