import GeometricTypicalLink

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Filter
open scoped Topology

/-- The sole input is a constant bound on the failure probability for
a uniformly random rooted link. There is no union over all links. -/
def AverageRootCutAt (t X : ℝ) (N : ℕ) : Prop :=
  ∃ d0 : 0<graphDimension X (N:ℝ),
    letI : Nontrivial (HostAmbient X N) :=
      Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
    (∑ v : Fin N, Moment.mean (sphericalHostWeight (V:=Fin N) (E:=HostAmbient X N) t)
      (fun g => if v∈failingRoots g then 1 else 0)) ≤ (N:ℝ)/(288^2)

theorem eventual_triangle_relative_variance (t X : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (Xp : 0<X) (hx : edgeRateClosed t+capRate t<X) :
    ∃ B : ℝ, ∀ (N : ℕ), B≤(N:ℝ) →
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E],
    Module.finrank ℝ E=graphDimension X N →
    let μ := (N.choose 3:ℝ)*(patternMass (E:=E) triangleCon t).toReal
    0<μ ∧ (4/μ^2)*Moment.mean (sphericalHostWeight (V:=Fin N) (E:=E) t)
      (fun g => (((triangles g).card:ℝ)-μ)^2) ≤ 1/4 := by
  classical
  obtain ⟨η,B,η0,_,rate⟩ := rooted_power_errors t X t0 ts Xp hx
  obtain ⟨C,c⟩ := eventually_atTop.mp
    ((tendsto_rpow_neg_atTop η0).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4608)))
  refine ⟨max 4 (max B C),?_⟩
  intro N Nlarge E _ _ _ _ _ _ d μ
  have nb : B≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans Nlarge)
  have nc : C≤(N:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans Nlarge)
  have n4 : 4≤N := by exact_mod_cast (le_max_left (4:ℝ) (max B C)).trans Nlarge
  let u := (patternMass (E:=E) triangleCon t).toReal
  let q := (patternMass (E:=E) diamondEdges t).toReal
  let p := sphericalHostWeight (V:=Fin N) (E:=E) t
  obtain ⟨u0,T,D⟩ := rate N nb E d
  have n1 : 1≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  have np : 0<(N:ℝ) := by positivity
  have ur : (N:ℝ)^2*u ≤ (N:ℝ)^3*u := by
    have nn := mul_le_mul_of_nonneg_left n1 (show 0≤(N:ℝ)^2*u by positivity)
    nlinarith only [nn]
  have qr : (N:ℝ)*u^2 ≤ (N:ℝ)^2*u^2 := by
    have nn := mul_le_mul_of_nonneg_left n1 (show 0≤(N:ℝ)*u^2 by positivity)
    nlinarith only [nn]
  have T' := (div_le_div_of_nonneg_left (show (0:ℝ)≤1 by norm_num) (by positivity) ur).trans T
  have D' := (div_le_div_of_nonneg_left (show 0≤q by exact ENNReal.toReal_nonneg)
    (by positivity) qr).trans D
  let R := (N:ℝ)^(-η)
  have r0 : 0≤R := Real.rpow_nonneg np.le _
  have n := moment_error_from_four N n4 1 u q 0 0 R (by norm_num) u0
    ENNReal.toReal_nonneg le_rfl le_rfl r0 T' D' (by simpa using r0) (by simpa using r0)
  simp only [mul_zero,add_zero,div_one] at n
  have v := variance_actual_triangles_upper p
    (sphericalHostWeight_probability (V:=Fin N) (E:=E) t).2 id u q
    ENNReal.toReal_nonneg
    (fun i hi => triangle_moment_exact t i (mem_powersetCard.mp hi).2)
    (fun i j hi hj ne r => (nonedge_overlap_triangle_moments t i j
      (mem_powersetCard.mp hi).2 (mem_powersetCard.mp hj).2 ne r).le)
    (fun i j hi hj _ r => (diamond_moment_overlap_two t i j
      (mem_powersetCard.mp hi).2 (mem_powersetCard.mp hj).2 r).le)
  simp only [Fintype.card_fin,id_eq] at v
  have C0 : 0<(N.choose 3:ℝ) :=
    (show 0<(N:ℝ)^3/48 by positivity).trans_le (choose_three_cubic N n4)
  refine ⟨mul_pos C0 u0,?_⟩
  dsimp [μ]
  exact (mul_le_mul_of_nonneg_left v (by positivity)).trans
    (n.trans (by have l : R<1/4608 := c N nc; linarith only [l]))

theorem folkman_given_typical_root_cuts (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (supply : ∀ X : ℝ, 0<X → edgeRateClosed t+capRate t<X →
      ∀ B : ℝ, ∃ N : ℕ, B≤(N:ℝ) ∧ AverageRootCutAt t X N) :
    ∃ N : ℕ, ∃ G' : EdgeGraph (Fin N), ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset (Fin N)→Bool, ∃ tri∈triangles G', Monochrom c tri := by
  classical
  apply folkman_given_cap_margin t (1/32) t0 ts (by norm_num)
  intro X Xp hx B
  obtain ⟨S,sec⟩ := eventual_relative_link_second t X t0 ts Xp hx
  obtain ⟨T,var⟩ := eventual_triangle_relative_variance t X t0 ts Xp hx
  obtain ⟨N,large,d0,bad⟩ := supply X Xp hx (max 4 (max B (max S T)))
  letI : Nontrivial (HostAmbient X N) :=
    Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
  have size : 1≤N := by
    exact_mod_cast (show (1:ℝ)≤N from (by norm_num : (1:ℝ)≤4).trans ((le_max_left _ _).trans large))
  let E := HostAmbient X N
  have b : max B (max S T)≤(N:ℝ) := (le_max_right _ _).trans large
  have dim : Module.finrank ℝ E=graphDimension X N := by simp [E,HostAmbient]
  obtain ⟨r0,rq⟩ := sec N ((le_max_left _ _).trans ((le_max_right _ _).trans b)) E dim
  obtain ⟨μ0,vq⟩ := var N ((le_max_right _ _).trans ((le_max_right _ _).trans b)) E dim
  let u := (patternMass (E:=E) triangleCon t).toReal
  let r := ((N-1).choose 2:ℝ)*u
  let μ := (N.choose 3:ℝ)*u
  have rr : (Fintype.card (Fin N):ℝ)*r=3*μ := by
    simp only [Fintype.card_fin]
    dsimp [r,μ]
    nlinarith only [congrArg (fun z : ℝ => z*u) (rootTriple_double_count N size)]
  refine ⟨N,(le_max_left _ _).trans b,d0,?_⟩
  exact typical_link_failure_reduction _ (sphericalHostWeight_probability (V:=Fin N) (E:=E) t).1
    r μ r0 μ0 rr rq (by simpa only [Fintype.card_fin] using bad) vq

#print axioms folkman_given_typical_root_cuts
end RobustFolkman.GeometricGap
