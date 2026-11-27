import GeometricRootedPower
namespace RobustFolkman.GeometricGap
open MeasureTheory Filter Finset
open scoped Topology

theorem rootTriple_double_count (n : ℕ) (hn : 1≤n) :
    (n:ℝ)*((n-1).choose 2:ℝ)=3*(n.choose 3:ℝ) := by
  have e := Nat.add_one_mul_choose_eq (n-1) 2
  have nn : n-1+1=n := by omega
  rw [nn,Nat.mul_comm (n.choose (2+1))] at e
  exact_mod_cast e

theorem root_variance_relative (n : ℕ) (hn : 4≤n) (u q : ℝ) (u0 : 0<u) (q0 : 0≤q)
    (T : 1/((n:ℝ)^2*u)≤1/64) (D : q/((n:ℝ)*u^2)≤1/64) :
    let A : ℝ := (n-1).choose 2
    A*(u+(↑(3*(n-3)):ℝ)*q) ≤ (A*u)^2 := by
  intro A
  have n0 : 0<(n:ℝ) := by positivity
  have a : (n:ℝ)^2/16≤A := by
    have e := rootTriple_double_count n (by omega)
    change (n:ℝ)*A=3*(n.choose 3:ℝ) at e
    have ec := choose_three_cubic n hn
    by_contra! h
    have hh := mul_lt_mul_of_pos_left h n0
    nlinarith only [e,ec,hh]
  have A0 : 0≤A := by positivity
  have mT := (div_le_iff₀ (mul_pos (pow_pos n0 _) u0)).mp T
  have mD := (div_le_iff₀ (mul_pos n0 (pow_pos u0 _))).mp D
  have t' := mul_le_mul_of_nonneg_right mT u0.le
  have d' := mul_le_mul_of_nonneg_left mD (show 0≤3*(n:ℝ) by positivity)
  have mulA := mul_le_mul_of_nonneg_right a (sq_nonneg u)
  have e : (↑(3*(n-3)):ℝ)≤3*(n:ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n 3) (by norm_num)
  have e' := mul_le_mul_of_nonneg_right e q0
  have m : u+(↑(3*(n-3)):ℝ)*q≤A*u^2 := by nlinarith only [t',d',mulA,e']
  have m' := mul_le_mul_of_nonneg_left m A0
  nlinarith only [m']

theorem eventual_relative_link_second (t X : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (Xp : 0<X) (hx : edgeRateClosed t+capRate t<X) :
    ∃ B : ℝ, ∀ (N : ℕ), B≤(N:ℝ) →
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
    Module.finrank ℝ E=graphDimension X N →
    let r := ((N-1).choose 2:ℝ) * (patternMass (E:=E) triangleCon t).toReal
    0<r ∧ ∀ v : Fin N, Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => linkTriangleCount g v ^ 2) ≤ 2*r^2 := by
  obtain ⟨η,B,η0,_,rate⟩ := rooted_power_errors t X t0 ts Xp hx
  obtain ⟨C,c⟩ := eventually_atTop.mp
    ((tendsto_rpow_neg_atTop η0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/64)))
  refine ⟨max 4 (max B C),?_⟩
  intro N Nlarge E _ _ _ _ _ _ d r
  have nb : B≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans Nlarge)
  have nc : C≤(N:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans Nlarge)
  have n4 : 4≤N := by exact_mod_cast (le_max_left (4:ℝ) (max B C)).trans Nlarge
  obtain ⟨u0,T,D⟩ := rate N nb E d
  have A0 : 0<(↑((N-1).choose 2):ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2≤N-1)
  refine ⟨mul_pos A0 u0,fun v => ?_⟩
  have sec := rootedLink_secondMoment (E:=E) t v
  have rel := root_variance_relative N n4 _ _ u0 ENNReal.toReal_nonneg
    (T.trans (c N nc).le) (D.trans (c N nc).le)
  simp only [Fintype.card_fin] at sec
  dsimp only at sec rel
  dsimp [r]
  linarith only [sec,rel]

#print axioms eventual_relative_link_second
end RobustFolkman.GeometricGap
