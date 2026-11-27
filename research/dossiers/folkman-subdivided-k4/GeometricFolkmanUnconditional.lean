import GeometricShellSample
import GeometricShellDimension
import GeometricShellSmallLoss
import GeometricRootShellTransfer
import GeometricSampleAsymptotic

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset WithLp Filter
open scoped ENNReal BigOperators Matrix.Norms.L2Operator InnerProductSpace Topology

theorem supply_typical_root_cuts (t : ℝ) (tp : 0<t) (ts : t≤1/40000)
    (small : ∀ r : ℝ, 0<r → let c := t/(1+t); let w := 100/(r*t); let s := 4*t*w;
      (4*r*c*s)*Real.exp (3+4*r*c*s)≤shellTolerance)
    (X : ℝ) (Xp : 0<X) (Xg : edgeRateClosed t+capRate t<X) (B : ℝ) :
    ∃ N : ℕ, B≤(N:ℝ) ∧ AverageRootCutAt t X N := by
  classical
  let C := 2*Real.exp 3
  let k := 1/(4*C)
  let δ : ℝ := 1/300000
  have Cp : 0<C := by dsimp [C]; positivity
  have kp : 0<k := by dsimp [k]; positivity
  have δp : 0<δ := by dsimp [δ]; norm_num
  have Cx : 0<1/X+1 := by positivity
  obtain ⟨η,T,ηp,T1,degree⟩ := polynomial_residual_degree t X tp ts Xp Xg
  obtain ⟨D,D1,dimLaw⟩ := eventual_shell_dimension t X tp ts Xp
  obtain ⟨F,F1,tail⟩ := spherical_tail_eventually_small (1/X+1) k η δ Cx kp ηp δp
  have gr : Tendsto (fun x : ℝ => k*x^η) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos kp).2 (tendsto_rpow_atTop ηp)
  obtain ⟨U,hU⟩ := eventually_atTop.1 (gr.eventually_ge_atTop (max 100 (2/δ)))
  let m₀ : ℕ := ⌈max 2 (max B (max T (max D (max F U))))⌉₊
  let N := m₀+1
  have hm₀ : max 2 (max B (max T (max D (max F U))))≤(m₀:ℝ) := Nat.le_ceil _
  have mn : (m₀:ℝ)≤N := by exact_mod_cast (Nat.le_succ m₀)
  have hn := hm₀.trans mn
  have n2 : (2:ℝ)≤m₀ := (le_max_left _ _).trans hm₀
  have hb : B≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have ht : T≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hd : D≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hf : F≤(N:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))))
  have hu : U≤(N:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))))
  have np : 0<(N:ℝ) := by dsimp [N]; positivity
  have half : (N:ℝ)/2≤m₀ := by dsimp [N]; push_cast; linarith only [n2]
  let n := graphDimension X (N:ℝ)-4
  let m := n+1
  let c := t/(1+t)
  let r := (m:ℝ)/2
  let w := 100/(r*t)
  have dr := dimLaw N hd
  change graphDimension X N=n+4 ∧ (n:ℝ)≤(1/X+1)*Real.log N ∧
    36≤(n:ℝ)/2 ∧ 100≤r*t^2 ∧ 3≤(n:ℝ)/2 ∧ 1≤4*((n:ℝ)/2)*c^2 ∧
    Real.sqrt (squaredCapContraction n c)≤1/200 at dr
  obtain ⟨d,nd,rL,rW,nL,nD,gap⟩ := dr
  have d0 : 0<graphDimension X N := by omega
  have rp : 0<r := by dsimp [r,m]; positivity
  have ts' : t≤1/8 := ts.trans (by norm_num)
  obtain ⟨w0,wt,wide,wh,cp,cs,s0,st⟩ := shell_width_valid t r tp ts rp rW
  let E := HostAmbient X N
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [E,HostAmbient] using d0)
  have edim : Module.finrank ℝ E=graphDimension X N := by simp [E,HostAmbient]
  have hh : ∀ a : UnitSphere E, (Measure.pi (fun _ : Fin m₀ => uniformSphere (volume : Measure E))).real
      {y | sampleBadCut t a y}≤1/(288^2:ℝ) := by
    intro a
    obtain ⟨K,e,rot,ndim⟩ := root_shell_isometry a
    let W := ↥Kᗮ
    have ddW : Module.finrank ℝ W=n+3 := by dsimp [W]; omega
    letI : Nontrivial W := Module.nontrivial_of_finrank_pos (R:=ℝ) (by omega)
    let S := SphereAmbient (Fin 1) W
    have dS : Module.finrank ℝ S=n+4 := by
      have h := e.toLinearEquiv.finrank_eq
      change Module.finrank ℝ E=Module.finrank ℝ S at h
      omega
    letI : Nontrivial S := e.injective.nontrivial
    let a' := sphereTransport e a
    have ra (x : UnitSphere S) : sphereHeight x=⟪a'.val,x.val⟫_ℝ := by
      obtain ⟨y,rfl⟩ := (sphereTransport e).surjective x
      simpa only [a',sphereTransport_val,e.inner_map_map] using rot y
    let b : UnitSphere W := residualDirection (0:W)
    let σ := uniformSphere (volume : Measure S)
    let τ := uniformSphere (volume : Measure W)
    let P := σ.real (shellBand t w)
    let q := τ.real (capPoints c b)
    letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
    letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
    obtain ⟨Pp,Pa,cP,removed⟩ := shell_small_loss_bound n ddW dS t tp ts a' ra b rL rW nL nD small
    have cp' : 0<c := by dsimp [c]; positivity
    have c8 : c≤1/8 := cs.trans (by norm_num)
    have cq : 0<q := ENNReal.toReal_pos
      (capPoints_both_positive c (by linarith only [cp']) (by linarith only [c8]) b).1.ne'
      (measure_ne_top τ _)
    have q1 : q≤1 := by
      have h := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=τ) (s:=capPoints c b))
      exact h.trans_eq ENNReal.toReal_one
    have dw : Module.finrank ℝ W+1=graphDimension X N := by omega
    have scale := degree N ht E W edim dw
    have Pcap : (patternMass (E:=E) edgeCon t).toReal≤C*P := by
      have h := congrArg ENNReal.toReal (capPoints_edge_mass t a)
      change (patternMass (E:=E) edgeCon t).toReal=(uniformSphere (volume : Measure E)).real (capPoints t a) at h
      rw [h,root_cap_probability_isometry e t a]
      exact cP
    have Qcap : (patternMass (E:=W) edgeCon c).toReal=q := congrArg ENNReal.toReal (capPoints_edge_mass c b)
    rw [Qcap] at scale
    have Bscale : (N:ℝ)^η ≤ (N:ℝ)*(C*P)*q :=
      scale.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Pcap np.le) cq.le)
    have g0 : k*(N:ℝ)^η≤((m₀:ℝ)*P/2)*q := by
      have h := mul_le_mul_of_nonneg_left Bscale kp.le
      have z := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right half Pp.le) cq.le
      have norm : k*((N:ℝ)*(C*P)*q)=(N:ℝ)*P*q/4 := by
        dsimp [k]
        field_simp [Cp.ne']
      rw [norm] at h
      nlinarith only [h,z]
    have power := hU (N:ℝ) hu
    have h100 : 100≤((m₀:ℝ)*P/2)*q := ((le_max_left _ _).trans power).trans g0
    have hδ : 2/δ≤((m₀:ℝ)*P/2)*q := ((le_max_right _ _).trans power).trans g0
    have mp0 : 0<(m₀:ℝ)*P := mul_pos (by linarith only [n2]) Pp
    have δ₁ : 4/((m₀:ℝ)*P)≤δ := by
      have z := mul_le_mul_of_nonneg_left q1 (show 0≤(m₀:ℝ)*P/2 by positivity)
      have w := (div_le_iff₀ δp).1 (hδ.trans (z.trans_eq (mul_one _)))
      apply (div_le_iff₀ mp0).2
      calc
        (4:ℝ) = 2*2 := by norm_num
        _ ≤ 2*((m₀:ℝ)*P/2*δ) := mul_le_mul_of_nonneg_left w (by norm_num)
        _ = δ*((m₀:ℝ)*P) := by ring
    have qmin : 1/(8*(2:ℝ)^n)≤q := by
      have z := (cap_simple_grid_lower n ddW c c8 b).2
      have eq : (1/8:ℝ)*(1/2)^n=1/(8*(2:ℝ)^n) := by
        rw [div_pow,one_pow]
        ring
      rwa [←eq]
    have estim (L : Finset (Fin m₀)) (lh : (m₀:ℝ)*P/2≤(L.card:ℝ)) :
        (Measure.pi (fun _ : {i : Fin m₀ // i∈L} => τ)).real
          {y | 4*(L.card:ℝ)*q/50<‖centeredSample (capKernel c) q y‖}≤δ := by
      have Lq : ((m₀:ℝ)*P/2)*q≤(L.card:ℝ)*q := mul_le_mul_of_nonneg_right lh cq.le
      have L100 := h100.trans Lq
      have lp : 0<L.card := by
        by_contra! h
        have hz : L.card=0 := by omega
        rw [hz,Nat.cast_zero,zero_mul] at L100
        norm_num at L100
      let L₀ := L.card-1
      have l : L₀+1=L.card := by dsimp [L₀]; omega
      have ci : Fintype.card {i : Fin m₀ // i∈L}=L₀+1 := by rw [Fintype.card_coe,l]
      have h := spherical_ambient_sample_tail (J:={i : Fin m₀ // i∈L}) n L₀ ddW ci c cp' c8 b nL nD gap
      change 100≤((L₀+1:ℕ):ℝ)*q→_ at h
      rw [l] at h
      have LL : (L.card:ℝ)≤N := by exact_mod_cast ((L.card_le_univ.trans_eq (Fintype.card_fin m₀)).trans (Nat.le_succ _))
      exact (h L100).trans (tail N hf n L.card q nd LL qmin (g0.trans Lq))
    have cb := shell_sample_bad_cut_bound (J:=Fin m₀) m (by dsimp [m]; omega)
      t w (5*shellTolerance) δ tp ts' w0 wt δp.le
      (by rw [Fintype.card_fin]; exact_mod_cast (show (0:ℝ)<m₀ by linarith only [n2]))
      a' ra b Pp Pa cq q1 (by simpa only [Fintype.card_fin] using h100)
      removed (by simpa only [Fintype.card_fin] using estim)
    have sum : 4/((m₀:ℝ)*P)+δ+100*(5*shellTolerance)≤1/(288^2:ℝ) := by
      dsimp [δ] at δ₁
      norm_num [δ,shellTolerance] at *
      linarith only [δ₁]
    rw [root_sample_bad_probability_isometry e t a]
    exact cb.trans (by simpa only [Fintype.card_fin] using sum)
  refine ⟨N,hb,d0,?_⟩
  calc
    _ ≤ ∑ _ : Fin N, 1/(288^2:ℝ) := Finset.sum_le_sum fun v _ =>
      typical_root_bound_from_conditionals m₀ t _ (by norm_num) v hh
    _ = _ := by simp [div_eq_mul_inv,nsmul_eq_mul]

/-- A finite triangle-Ramsey graph without a once-subdivided K₄ as a
not-necessarily-induced subgraph. -/
theorem folkman_without_subdivided_k4 :
    ∃ N : ℕ, ∃ G : EdgeGraph (Fin N), ¬Paraglider.Contains (hasEdge G) ∧
      ∀ c : Finset (Fin N)→Bool, ∃ tri∈triangles G,Monochrom c tri := by
  obtain ⟨t,tp,ts,sm⟩ := choose_small_shell_threshold 100 shellTolerance (by norm_num)
    (by norm_num [shellTolerance])
  exact folkman_given_typical_root_cuts t tp ts (supply_typical_root_cuts t tp ts sm)

#print axioms folkman_without_subdivided_k4
end RobustFolkman.GeometricGap
