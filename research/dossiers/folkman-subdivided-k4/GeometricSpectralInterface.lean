import GeometricDirectedLinkSum

namespace RobustFolkman.GeometricGap
open Matrix Finset MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rootedLink_two (g : EdgeGraph V) (v : V) (e : Finset V)
    (he : e∈rootedLinkEdges g v) : e.card=2 := by
  obtain ⟨T,ht,rfl⟩ := mem_image.mp he
  obtain ⟨tr,rt⟩ := mem_filter.mp ht
  obtain ⟨a,b,d,ab,ad,bd,rfl⟩ := (mem_triangles.mp tr).2
  rw [Finset.card_erase_of_mem rt,triple_vertices_exact,
    Finset.card_eq_three.mpr ⟨a,b,d,ab,ad,bd,rfl⟩]

def LinkLowerSpectrum (g : EdgeGraph V) (ρ : ℝ) : Prop :=
  ∀ (v : V) (x : V→ℝ),
    -ρ*(∑ i, (x i)^2) ≤ x ⬝ᵥ (normAdj (linkAdjMatrix (rootedLinkEdges g v)) *ᵥ x)

theorem lower_link_spectrum_margin (g : EdgeGraph V) (ρ : ℝ) (h : LinkLowerSpectrum g ρ) :
    coloringMargin ((1-3*ρ)/4) g=true := by
  apply margin_from_actual_link_maxcut
  intro v b
  let L := rootedLinkEdges g v
  let W := linkAdjMatrix L
  have two := rootedLink_two g v
  have bd := weighted_cut_from_normalized_lower_spectrum W (linkAdjMatrix_symm L)
    (linkAdjMatrix_nonneg L) b ρ (h v)
  change (∑ i, ∑ j, linkAdjMatrix L i j*edgeFlip b i j)≤
    ((1+ρ)/2)*(∑ i, ∑ j, linkAdjMatrix L i j) at bd
  rw [directed_cut_count L two b,directed_orient_count L two] at bd
  unfold rootedLinkCut
  linarith only [bd]

/-- The missing analytic bound needs only the bottom of each normalized
link spectrum, not a two-sided norm estimate or an upper eigenvalue gap. -/
def BottomLinkFailureAt (t X ρ : ℝ) (N : ℕ) : Prop :=
  ∃ d0 : 0<graphDimension X (N:ℝ),
    letI : Nontrivial (HostAmbient X N) :=
      Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
    Moment.mean (sphericalHostWeight (V:=Fin N) (E:=HostAmbient X N) t)
      (fun g => @ite ℝ (¬LinkLowerSpectrum g ρ) (Classical.propDecidable _) 1 0) ≤ 1/2

theorem bottom_link_margin_at (t X ρ : ℝ) (N : ℕ) (hyp : BottomLinkFailureAt t X ρ N) :
    CapMarginAt t ((1-3*ρ)/4) X N := by
  classical
  obtain ⟨d0,h⟩ := hyp
  letI : Nontrivial (HostAmbient X N) :=
    Module.nontrivial_of_finrank_pos (R:=ℝ) (by simpa [HostAmbient] using d0)
  refine ⟨d0,?_⟩
  apply le_trans ?_ h
  unfold Moment.mean
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_left _ ((sphericalHostWeight_probability (V:=Fin N) (E:=HostAmbient X N) t).1 g)
  by_cases ng : LinkLowerSpectrum g ρ
  · simp [ng,Moment.bad,lower_link_spectrum_margin g ρ ng]
  · simp [ng,Moment.bad]
    split <;> norm_num

theorem folkman_given_bottom_link_failure (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (supply : ∀ X : ℝ, 0<X → edgeRateClosed t+capRate t<X →
      ∀ B : ℝ, ∃ N : ℕ, B≤(N:ℝ) ∧ BottomLinkFailureAt t X (1/4) N) :
    ∃ N : ℕ, ∃ G' : EdgeGraph (Fin N), ¬Paraglider.Contains (hasEdge G') ∧
      ∀ c : Finset (Fin N)→Bool, ∃ tri∈triangles G', Monochrom c tri := by
  apply folkman_given_cap_margin t ((1-3*(1/4))/4) t0 ts (by norm_num)
  intro X Xp gate B
  obtain ⟨N,hN,h⟩ := supply X Xp gate B
  exact ⟨N,hN,bottom_link_margin_at t X (1/4) N h⟩

#print axioms folkman_given_bottom_link_failure
end RobustFolkman.GeometricGap
