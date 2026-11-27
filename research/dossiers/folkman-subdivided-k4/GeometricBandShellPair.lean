import GeometricBandPairLaw
import GeometricShellBudget
import GeometricRootedShellLoss

namespace RobustFolkman.GeometricGap
open MeasureTheory Set WithLp
open scoped ENNReal InnerProductSpace
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W]
local notation "S" => UnitSphere (SphereAmbient (Fin 1) W)

def shellBand (t w : ℝ) : Set S := sphereHeight ⁻¹' Icc t (t+w)

def shellPair (t w c : ℝ) : Set (S×S) :=
  (Prod.map sphereResidual sphereResidual) ⁻¹' pairCap c ∩
    (shellBand t w ×ˢ shellBand t w)

theorem shellBand_measurable (t w : ℝ) : MeasurableSet (shellBand (W:=W) t w) :=
  sphereHeight_measurable measurableSet_Icc

theorem shellPair_measurable (t w c : ℝ) : MeasurableSet (shellPair (W:=W) t w c) :=
  ((sphereResidual_measurable.prodMap sphereResidual_measurable) (pairCap_measurable c)).inter
    ((shellBand_measurable t w).prod (shellBand_measurable t w))

theorem shellPair_tight_subset (t w : ℝ) (tp : 0<t) (ts : t≤1/8)
    (w0 : 0≤w) (wt : w≤t) (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) :
    shellPair t w (t/(1+t))⊆triangleAt t a := by
  intro p hp
  obtain ⟨h,hl,hr⟩ := hp
  change t≤sphereHeight p.1 ∧ sphereHeight p.1≤t+w at hl
  change t≤sphereHeight p.2 ∧ sphereHeight p.2≤t+w at hr
  have br := actual_shell_link_bracket p.1 p.2 t w tp ts w0 wt hl.1 hl.2 hr.1 hr.2
  exact ⟨by simpa only [ha] using hl.1,by simpa only [ha] using hr.1,br.1 h⟩

theorem shellPair_triangle_subset (t w : ℝ) (tp : 0<t) (ts : t≤1/8)
    (w0 : 0≤w) (wt : w≤t) (a : S) (ha : ∀ x : S, sphereHeight x=⟪a.val,x.val⟫_ℝ) :
    triangleAt t a ⊆ lostRootTriangle t w a ∪ shellPair t w (t/(1+t)-4*t*w) := by
  intro p hp
  by_cases h : p∈lostRootTriangle t w a
  · exact Or.inl h
  · apply Or.inr
    have hcopy := hp
    obtain ⟨h1,h2,h3⟩ := hp
    have b1 : sphereHeight p.1≤t+w := by
      rw [ha]
      apply le_of_lt
      apply lt_of_not_ge
      exact fun u => h ⟨hcopy,Or.inl u⟩
    have b2 : sphereHeight p.2≤t+w := by
      rw [ha]
      apply le_of_lt
      apply lt_of_not_ge
      exact fun u => h ⟨hcopy,Or.inr u⟩
    have a1 : t≤sphereHeight p.1 := (ha p.1).symm ▸ h1
    have a2 : t≤sphereHeight p.2 := (ha p.2).symm ▸ h2
    exact ⟨(actual_shell_link_bracket p.1 p.2 t w tp ts w0 wt a1 b1 a2 b2).2 h3,
      ⟨a1,b1⟩,⟨a2,b2⟩⟩

theorem shellPair_pullback (m : ℕ) (dim : Module.finrank ℝ W=m+2) (t w : ℝ)
    (B : Set (UnitSphere W×UnitSphere W)) (Bm : MeasurableSet B) :
    let σ := uniformSphere (volume : Measure (SphereAmbient (Fin 1) W))
    let P := σ (shellBand t w)
    let τ := uniformSphere (volume : Measure W)
    P≠0 →
    (σ.prod σ) ((Prod.map sphereResidual sphereResidual) ⁻¹' B ∩
      (shellBand t w ×ˢ shellBand t w)) = P^2*(τ.prod τ) B := by
  let H := (fun x : Fin 1→ℝ => x 0) ⁻¹' Icc t (t+w)
  have hm : MeasurableSet H := measurable_pi_apply 0 measurableSet_Icc
  exact band_residual_pair_mass m dim H hm B Bm

#print axioms shellPair_tight_subset
#print axioms shellPair_triangle_subset
#print axioms shellPair_pullback
end RobustFolkman.GeometricGap
