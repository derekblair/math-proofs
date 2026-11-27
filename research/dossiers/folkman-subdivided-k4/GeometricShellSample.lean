import GeometricRetainedGraph
import GeometricRootedSample
import GeometricShellRemoval
import GeometricGraphLossTail
import GeometricBandCountLower

namespace RobustFolkman.GeometricGap
open MeasureTheory Set Finset WithLp Matrix
open scoped ENNReal BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
local notation "S" => UnitSphere (SphereAmbient (Fin 1) W)

theorem shell_sample_bad_cut_bound (m : ℕ) (dim : Module.finrank ℝ W=m+2)
    (t w r δ : ℝ) (tp : 0<t) (ts : t≤1/8) (w0 : 0≤w) (wt : w≤t)
    (δ0 : 0≤δ) (j0 : 0<Fintype.card J)
    (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) (b : UnitSphere W) :
    let c := t/(1+t)
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let τ := uniformSphere (volume : Measure W)
    let A := shellBand t w
    let P := σ.real A
    let q := τ.real (capPoints c b)
    let N := Fintype.card J
    let μ := Measure.pi (fun _ : J => σ)
    0<P → σ Aᶜ≠0 → 0<q → q≤1 → 100≤((N:ℝ)*P/2)*q →
    (σ.prod σ).real (triangleAt t a\shellPair t w c)≤r*P^2*q →
    (∀ L : Finset J, (N:ℝ)*P/2≤(L.card:ℝ) →
      (Measure.pi (fun _ : {i : J // i∈L} => τ)).real
        {y | 4*(L.card:ℝ)*q/50<‖centeredSample (capKernel c) q y‖}≤δ) →
    μ.real {x | sampleBadCut t a x}≤4/((N:ℝ)*P)+δ+100*r := by
  classical
  intro c σ τ A P q N μ Pp A1 qp q1 Npq loss rad
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  have A0 : σ A≠0 := by exact (ENNReal.toReal_pos_iff.1 Pp).1.ne'
  let Lgood := fun L : Finset J => (N:ℝ)*P/2≤(L.card:ℝ)
  let Bad := fun L : Finset J => {y : {i : J // i∈L}→UnitSphere W |
    4*(L.card:ℝ)*q/50<‖centeredSample (capKernel c) q y‖}
  let U := {x : J→S | ((retained A x).card:ℝ)<(N:ℝ)*P/2}
  let V := ⋃ L ∈ (Finset.univ.filter Lgood : Finset (Finset J)),
    {x : J→S | retained A x=L ∧ (fun i : {i : J // i∈L} => sphereResidual (x i.val))∈Bad L}
  let G := triangleAt t a
  let K := shellPair (W:=W) t w c
  let M := (N:ℝ)^2*P^2*q
  let Z := {x : J→S | M/100<((samplePredicateGraph G x \ samplePredicateGraph K x).card:ℝ)}
  have nP : 0<(N:ℝ)*P := mul_pos (by exact_mod_cast j0) Pp
  have rU : μ.real U≤4/((N:ℝ)*P) := retained_below_half_mean σ A (shellBand_measurable t w) nP
  have rV : μ.real V≤δ := by
    let H := (fun x : Fin 1→ℝ => x 0) ⁻¹' Icc t (t+w)
    have hm : MeasurableSet H := measurable_pi_apply 0 measurableSet_Icc
    have f (L : Finset J) (lh : Lgood L) :
        (Measure.pi (fun _ : {i : J // i∈L} => τ)) (Bad L)≤ENNReal.ofReal δ := by
      have z := ENNReal.ofReal_le_ofReal (rad L lh)
      rwa [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at z
    have h := band_bad_mixture m dim H hm Lgood Bad
      (fun L => measurable_bad_sphere_norm c q _) (ENNReal.ofReal δ) A0 A1 f
    change μ V≤ENNReal.ofReal δ at h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal δ0)
  have rZ : μ.real Z≤100*r := sample_graph_removed_tail σ G K (triangleAt_measurable t a)
    (shellPair_measurable t w c) P q r Pp qp j0 loss
  have incl : {x : J→S | sampleBadCut t a x}⊆(U∪V)∪Z := by
    intro x hx
    by_contra! no
    have nu : x∉U := fun hh => no (Or.inl (Or.inl hh))
    have nv : x∉V := fun hh => no (Or.inl (Or.inr hh))
    have nz : x∉Z := fun hh => no (Or.inr hh)
    let L := retained A x
    have lh : Lgood L := le_of_not_gt nu
    let y := fun i : {i : J // i∈L} => sphereResidual (x i.val)
    have norm : ‖centeredSample (capKernel c) q y‖≤4*(L.card:ℝ)*q/50 := by
      apply le_of_not_gt
      intro hh
      apply nv
      exact Set.mem_iUnion.2 ⟨L,Set.mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,lh⟩,rfl,hh⟩⟩
    have lq : 100≤(L.card:ℝ)*q := Npq.trans (mul_le_mul_of_nonneg_right lh qp.le)
    have lc : (100:ℝ)≤L.card := lq.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left q1
        (Nat.cast_nonneg L.card))
    have car : Fintype.card {i : J // i∈L}=L.card := Fintype.card_coe _
    have step := sample_graph_good_of_centeredSample c q qp.le
      (by rw [car]; exact lc) y (by rw [car]; exact norm)
    rw [car] at step
    let H := samplePredicateGraph K x
    let F := samplePredicateGraph G x
    have Hlift : H=liftEdges (Function.Embedding.subtype (fun i => i∈L)) (pointGraph c y) := by
      have e : K={p : S×S | p.1∈A ∧ p.2∈A ∧
          c≤⟪(sphereResidual p.1).val,(sphereResidual p.2).val⟫_ℝ} := by
        ext p
        simp [K,A,shellPair,pairCap,and_comm,and_left_comm]
      unfold H
      rw [e]
      exact band_tight_graph_lift A sphereResidual c x L (fun i => by simp [L,retained])
    have sub : H⊆F := samplePredicate_mono _ _ _ (shellPair_tight_subset t w tp ts w0 wt a ha)
    have lower : 9/80*M≤(H.card:ℝ) := by
      rw [Hlift,liftEdges_card]
      have ll := pow_le_pow_left₀ (by positivity : 0≤(N:ℝ)*P/2) lh 2
      have zz := mul_le_mul_of_nonneg_right ll (show 0≤9/20*q by positivity)
      dsimp [M]
      nlinarith only [zz,step.1]
    have cut : ∀ b : J→Bool, cutCount H b≤9/16*(H.card:ℝ) := by
      intro b
      rw [Hlift,liftEdges_cut,liftEdges_card]
      exact step.2 _
    have small : ((F\H).card:ℝ)≤M/100 := le_of_not_gt nz
    obtain ⟨b,hb⟩ := hx
    exact not_lt_of_ge (shell_budget_cut H F sub M (by dsimp [M]; positivity) lower small cut b) hb
  exact (measureReal_mono incl).trans ((measureReal_union_le (U∪V) Z).trans
    (add_le_add ((measureReal_union_le U V).trans (add_le_add rU rV)) rZ))

#print axioms shell_sample_bad_cut_bound
end RobustFolkman.GeometricGap
