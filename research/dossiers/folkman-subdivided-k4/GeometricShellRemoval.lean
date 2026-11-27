import GeometricBandShellPair

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
local notation "S" => UnitSphere (SphereAmbient (Fin 1) W)

theorem shell_removed_pair_mass (m : ℕ) (dim : Module.finrank ℝ W=m+2) (t w f ε : ℝ)
    (tp : 0<t) (ts : t≤1/8) (w0 : 0≤w) (wt : w≤t)
    (f0 : 0≤f) (fh : f≤1/2) (e0 : 0≤ε) (eh : ε≤1)
    (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) (b : UnitSphere W) :
    let c := t/(1+t)
    let s := 4*t*w
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let τ := uniformSphere (volume : Measure W)
    let P := σ.real (shellBand t w)
    let q := τ.real (capPoints c b)
    σ (shellBand t w) ≠ 0 →
    (σ.prod σ).real (lostRootTriangle t w a) ≤ f*(σ.prod σ).real (triangleAt t a) →
    (τ.prod τ).real (pairCap (c-s)\pairCap c)≤ε*q →
    (σ.prod σ).real (triangleAt t a\shellPair t w c)≤(4*f+ε)*P^2*q := by
  intro c s σ τ P q P0 lost gap
  letI : IsProbabilityMeasure σ := uniformSphere_isProbability _
  letI : IsProbabilityMeasure τ := uniformSphere_isProbability _
  let μ := σ.prod σ
  let U := shellPair (W:=W) t w (c-s)
  let K := shellPair (W:=W) t w c
  let G := triangleAt t a
  let L := lostRootTriangle t w a
  let q' := τ.real (capPoints (c-s) b)
  have g := shellPair_triangle_subset t w tp ts w0 wt a ha
  change G⊆L∪U at g
  have mass (v : ℝ) : (τ.prod τ) (pairCap v)=τ (capPoints v b) := pairCap_mass v b
  have loose : μ.real U=P^2*q' := by
    have h := shellPair_pullback m dim t w (pairCap (c-s)) (pairCap_measurable (c-s)) P0
    change μ U=σ (shellBand t w)^2*(τ.prod τ) (pairCap (c-s)) at h
    simp only [Measure.real,h,ENNReal.toReal_mul,ENNReal.toReal_pow,mass,P,q']
  have hs : pairCap (W:=W) c⊆pairCap (c-s) := by
    intro z hz
    exact (sub_le_self c (by dsimp [s]; positivity)).trans hz
  have ap : (τ.prod τ).real (pairCap (c-s)\pairCap c)=q'-q := by
    rw [measureReal_sdiff (μ:=τ.prod τ) hs (pairCap_measurable c)
      (measure_ne_top (τ.prod τ) _)]
    simp only [Measure.real,mass,q,q']
  have lg : μ.real (U\K)≤P^2*(q'-q) := by
    have e : U\K=(Prod.map sphereResidual sphereResidual) ⁻¹' (pairCap (c-s)\pairCap c) ∩
        (shellBand t w ×ˢ shellBand t w) := by
      ext x
      simp only [U,K,shellPair,mem_sdiff,mem_inter_iff,Set.mem_preimage,not_and]
      tauto
    have aeq := shellPair_pullback m dim t w (pairCap (c-s)\pairCap c)
      ((pairCap_measurable (c-s)).diff (pairCap_measurable c)) P0
    change μ _=σ (shellBand t w)^2*(τ.prod τ) (pairCap (c-s)\pairCap c) at aeq
    unfold Measure.real
    rw [e,aeq,ENNReal.toReal_mul,ENNReal.toReal_pow]
    exact mul_le_mul_of_nonneg_left ap.le (sq_nonneg P)
  have qbound : q'≤(1+ε)*q := by
    rw [ap] at gap
    linarith only [gap]
  have tg : (1-f)*μ.real G≤P^2*q' := by
    have h := (measureReal_mono (μ:=μ) g).trans (measureReal_union_le L U)
    rw [loose] at h
    linarith only [lost,h]
  have sub : G\K⊆L∪(U\K) := by
    intro z hz
    rcases g hz.1 with h|h
    · exact Or.inl h
    · exact Or.inr ⟨h,hz.2⟩
  exact (measureReal_mono (μ:=μ) sub).trans ((measureReal_union_le L (U\K)).trans
    (shell_loss_expected_bound P q q' (μ.real G) f ε (μ.real L) (μ.real (U\K))
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg f0 fh e0 eh tg qbound lost lg))

#print axioms shell_removed_pair_mass
end RobustFolkman.GeometricGap
