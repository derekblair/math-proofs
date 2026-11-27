import GeometricSaturated
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace RobustFolkman.GeometricGap
open Matrix Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem abs_entry_le_one (M : Matrix I I ℝ) (p : M.PosSemidef)
    (diag : ∀ i, M i i=1) (i j : I) : |M i j|≤1 := by
  let x : I→ℝ := Pi.single i 1
  let y : I→ℝ := Pi.single j 1
  have sym : M j i=M i j := by
    have h := congrFun (congrFun p.isHermitian.eq i) j
    simpa [Matrix.conjTranspose_apply] using h
  have qo (v : I→ℝ) : 0≤M.toBilin' v v := by
    simpa [Matrix.toBilin'_apply'] using p.dotProduct_mulVec_nonneg v
  have lo := qo (x+y)
  have hi := qo (x-y)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    x,y,Matrix.toBilin'_single,diag,sym] at lo hi
  exact abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩

theorem closed_gram_feasible (C : I→I→Prop) (t : ℝ) :
    IsClosed {M : Matrix I I ℝ | GramFeasible C t M} := by
  have ev (i j : I) : Continuous (fun M : Matrix I I ℝ => M i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have B (v : I→ℝ) : Continuous (fun M : Matrix I I ℝ => M.toBilin' v v) := by
    simp_rw [Matrix.toBilin'_apply]
    apply continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_const.mul (ev i j)).mul continuous_const
  have hs : IsClosed {M : Matrix I I ℝ | ∀ i j, M i j=M j i} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (ev i j) (ev j i)
  have hq : IsClosed {M : Matrix I I ℝ | ∀ v : I→ℝ, 0≤M.toBilin' v v} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (B v)
  have hd : IsClosed {M : Matrix I I ℝ | ∀ i, M i i=1} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (ev i i) continuous_const
  have hc : IsClosed {M : Matrix I I ℝ | ∀ i j, C i j → t≤M i j} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun j => ?_
    by_cases h : C i j
    · simpa [h] using isClosed_le (continuous_const (y:=t)) (ev i j)
    · simp [h]
  have eq : {M : Matrix I I ℝ | GramFeasible C t M} =
      ({M : Matrix I I ℝ | ∀ i j, M i j=M j i} ∩
      {M : Matrix I I ℝ | ∀ v : I→ℝ, 0≤M.toBilin' v v}) ∩
      ({M : Matrix I I ℝ | ∀ i, M i i=1} ∩
      {M : Matrix I I ℝ | ∀ i j, C i j → t≤M i j}) := by
    ext M
    have r : M.IsHermitian ↔ ∀ i j, M i j=M j i := by
      constructor
      · intro h i j
        simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun h.eq j) i)
      · intro h
        ext i j
        simpa [Matrix.conjTranspose_apply] using h j i
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,GramFeasible,Matrix.posSemidef_iff_dotProduct_mulVec,r,Matrix.toBilin'_apply',star_trivial,and_assoc]
  rw [eq]
  exact (hs.inter hq).inter (hd.inter hc)

theorem compact_gram_feasible (C : I→I→Prop) (t : ℝ) :
    IsCompact {M : Matrix I I ℝ | GramFeasible C t M} := by
  let cube : Set (Matrix I I ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1:ℝ) 1
  have cc : IsCompact cube := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine cc.of_isClosed_subset (closed_gram_feasible C t) ?_
  intro M h
  change GramFeasible C t M at h
  change ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → M i j ∈ Set.Icc (-1:ℝ) 1
  exact fun i _ j _ => abs_le.mp (abs_entry_le_one M h.1 h.2.1 i j)

theorem gram_max_exists (C : I→I→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (n : Fintype.card I≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/20000) :
    ∃ M : Matrix I I ℝ, GramFeasible C t M ∧ ∀ A, GramFeasible C t A → A.det≤M.det := by
  classical
  have h : ({M : Matrix I I ℝ | GramFeasible C t M} : Set _).Nonempty := by
    obtain ⟨M,h,_⟩ := probe_exists C sym n t t0 ts
    exact ⟨M,h⟩
  have detcont : Continuous (fun M : Matrix I I ℝ => M.det) := by
    simp_rw [Matrix.det_apply']
    apply continuous_finsetSum _ fun p _ => Continuous.mul continuous_const ?_
    exact continuous_finsetProd _ fun i _ => (continuous_apply i).comp (continuous_apply (p i))
  obtain ⟨M,hM,hmax⟩ := (compact_gram_feasible C t).exists_isMaxOn h detcont.continuousOn
  exact ⟨M,hM,fun _ hA => hmax hA⟩

#print axioms gram_max_exists
end RobustFolkman.GeometricGap
