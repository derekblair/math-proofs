import GeometricPatternReindex
import GeometricMomentBounds

namespace RobustFolkman.GeometricGap
open Matrix MeasureTheory
open scoped ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

def PowerRateWindow (C : I→I→Prop) (t : ℝ) (M : Matrix I I ℝ)
    (X δ N0 : ℝ) : Prop :=
  ∀ N : ℝ, N0≤N →
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E=graphDimension X N →
      N^(-patternRate M/X-δ) ≤ (patternMass (E:=E) C t).toReal ∧
      (patternMass (E:=E) C t).toReal ≤ N^(-patternRate M/X+δ)

theorem generic_power_rates (C : I→I→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (small : Fintype.card I≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (M : Matrix I I ℝ) (opt : GramOptimal C t M) (X δ : ℝ) (Xp : 0<X)
    (dp : 0<δ) : ∃ N0 : ℝ, 1≤N0 ∧ PowerRateWindow C t M X δ N0 := by
  let e := (Fintype.equivFin I).symm
  let F : Fin (Fintype.card I)→Fin (Fintype.card I)→Prop := fun i j => C (e i) (e j)
  let A := M.submatrix e e
  have op : GramOptimal F t A := gramOptimal_reindex e C t M opt
  obtain ⟨N0,hN,rate⟩ := sphere_pattern_power_rates F (fun i j => sym _ _) small t t0 ts
    A op.1 op.2 X δ Xp dp
  refine ⟨N0,hN,?_⟩
  intro N ge E _ _ _ _ _ _ d
  have mass : spherePatternMass (E:=E) F t = patternMass (E:=E) C t :=
    patternMass_reindex e C t
  have det : A.det=M.det := Matrix.det_submatrix_equiv_self e M
  have exp : -patternRate M/X=Real.log A.det/(2*X) := by rw [det]; unfold patternRate; ring
  rw [exp]
  simpa only [mass] using rate N ge E d

/-- For the triangle, diamond, forbidden pattern, and charged extension,
one choice of dimension and one threshold N0 control all four errors. -/
theorem joint_pattern_error_powers (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (Ee : Matrix (Fin 2) (Fin 2) ℝ)
    (Tr : Matrix (Fin 2⊕Unit) (Fin 2⊕Unit) ℝ)
    (Di : Matrix Four Four ℝ) (Ho : Matrix Five Five ℝ)
    (Jo : Matrix (Five⊕Unit) (Five⊕Unit) ℝ)
    (e : GramOptimal edgeCon t Ee) (tr : GramOptimal triangleCon t Tr)
    (d : GramOptimal diamondEdges t Di) (h : GramOptimal subEdges t Ho)
    (j : GramOptimal extCon t Jo) :
    ∃ X η N0 : ℝ, 0<X ∧ 0<η ∧ 1≤N0 ∧
      patternRate Ee+capRate t<X ∧
      ∀ N : ℝ, N0≤N →
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
      Module.finrank ℝ E=graphDimension X N →
      let u := (patternMass (E:=E) triangleCon t).toReal
      let v := (patternMass (E:=E) diamondEdges t).toReal
      let h := (patternMass (E:=E) subEdges t).toReal
      let j := (patternMass (E:=E) extCon t).toReal
      0<u ∧ (1/(N^3*u)≤N^(-η) ∧ v/(N^2*u^2)≤N^(-η) ∧
        N^2*h/u≤N^(-η) ∧ N^3*j/u≤N^(-η)) := by
  obtain ⟨id, X,Xp,cap,h2,j3,t3,d2⟩ := exact_pattern_rate_window t t0
    (by linarith only [ts]) Ee Tr Di Ho Jo e tr d h j
  obtain ⟨δ,η,dp,et,Bt,Bd,Bh,Bj⟩ := failure_exponent_room X
    (patternRate Tr) (patternRate Di) (patternRate Ho) (patternRate Jo) Xp t3 d2 h2 j3
  obtain ⟨NT,nt,Tlaw⟩ := generic_power_rates triangleCon triangleCon_sym (by decide) t t0 ts Tr tr X δ Xp dp
  obtain ⟨ND,nd,Dlaw⟩ := generic_power_rates diamondEdges diamond_sym (by decide) t t0 ts Di d X δ Xp dp
  obtain ⟨NH,nh,Hlaw⟩ := generic_power_rates subEdges subEdges_sym (by decide) t t0 ts Ho h X δ Xp dp
  obtain ⟨NJ,nj,Jlaw⟩ := generic_power_rates extCon extCon_sym (by decide) t t0 ts Jo j X δ Xp dp
  let N0 := max (max NT ND) (max NH NJ)
  have lT : NT≤N0 := (le_max_left _ _).trans (le_max_left _ _)
  have lD : ND≤N0 := (le_max_right _ _).trans (le_max_left _ _)
  have lH : NH≤N0 := (le_max_left _ _).trans (le_max_right _ _)
  have lJ : NJ≤N0 := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨X,η,N0,Xp,et,nt.trans lT,id ▸ cap,?_⟩
  intro N Nlarge E _ _ _ _ _ _ dd u v h j
  have n1 := nt.trans (lT.trans Nlarge)
  have T := (Tlaw N (lT.trans Nlarge) E dd).1
  have D := (Dlaw N (lD.trans Nlarge) E dd).2
  have H := (Hlaw N (lH.trans Nlarge) E dd).2
  have J := (Jlaw N (lJ.trans Nlarge) E dd).2
  refine ⟨(Real.rpow_pos_of_pos (zero_lt_one.trans_le n1) _).trans_le T,?_⟩
  exact four_failure_power_bounds N (-patternRate Tr/X) (-patternRate Di/X)
    (-patternRate Ho/X) (-patternRate Jo/X) δ η u v h j n1 T D H J Bt Bd Bh Bj

#print axioms joint_pattern_error_powers
end RobustFolkman.GeometricGap
