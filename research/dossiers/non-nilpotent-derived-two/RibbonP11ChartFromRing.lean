import RibbonP11Normalize
import RibbonAffineGroup
import Mathlib.RingTheory.Ideal.Maximal

namespace RibbonP11
open RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports
variable {G S K : Type*} [Group G] [CommRing S] [Field K]

theorem unique_max_units (f : S →+* K)
    (uniq : ∀ I : Ideal S, I.IsMaximal → I=RingHom.ker f) {a : S} (ha : f a≠0) :
    IsUnit a := by
  by_contra h
  have spanProper : Ideal.span ({a} : Set S) ≠ ⊤ := fun e =>
    h (Ideal.span_singleton_eq_top.mp e)
  obtain ⟨I,hI,L⟩ := Ideal.exists_le_maximal _ spanProper
  have H : a ∈ RingHom.ker f := by
    rw [←uniq I hI]
    exact L (Ideal.subset_span (by simp))
  exact ha H

private theorem residue_nontrivial (f : S →+* K) (μ : G →* Sˣ)
    (ell : D G →* Multiplicative S) (e : Equivariant μ ell)
    (x y : G) (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1)
    (stat : D G=LS G 2) : ∃ s, f (μ s:S)≠1 := by
  by_contra! no
  let φ : D G →* Multiplicative K := f.toAddMonoidHom.toMultiplicative.comp ell
  let N := φ.ker.map (D G).subtype
  have all : LS G 2 ≤ N := by
    change ⁅LS G 1,(⊤ : Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro d hd s _
    refine ⟨cAt d s,?_,rfl⟩
    change f (disp ell s d)=0
    rw [disp_derived μ ell e s ⟨d,hd⟩,map_mul,map_sub,map_one,no s,sub_self,zero_mul]
  have cN : portC x y∈N := all (stat ▸ layer_c x y)
  obtain ⟨d,hd,E⟩ := cN
  have Ed : d=⟨portC x y,layer_c x y⟩ := Subtype.ext E
  subst d
  change f (Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩))=0 at hd
  rw [c1,map_one] at hd
  exact one_ne_zero hd

private theorem pivot (f : S →+* K) (μ : G →* Sˣ) (x y : G) (gen : Generates x y)
    (nontrivial : ∃ s, f (μ s:S)≠1) : f (μ x:S)≠1 ∨ f (μ y:S)≠1 := by
  by_contra! n
  let F : G →* K := f.toMonoidHom.comp ((Units.coeHom S).comp μ)
  have L : Subgroup.closure ({x,y} : Set G) ≤ F.ker := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl|rfl
    · exact n.1
    · exact n.2
  change Subgroup.closure ({x,y} : Set G)=⊤ at gen
  rw [gen] at L
  obtain ⟨s,hs⟩ := nontrivial
  exact hs (L (Subgroup.mem_top s))

/-- Construct local affine coordinates in any quotient algebra for which
nonzero scalar residues lift to units. Covers the field and local jets. -/
theorem normalize_residue_model (f : S →+* K)
    (lifts : ∀ r : S, f r≠0 → IsUnit r)
    (μ : G →* Sˣ) (ell : D G →* Multiplicative S) (e : Equivariant μ ell)
    (x y : G) (gen : Generates x y)
    (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1)
    (stat : D G=LS G 2) :
    ∃ τ : G → S, IsCocycle μ τ ∧
      ((f (μ x:S)≠1 ∧ τ x=0 ∧ τ y=1) ∨
       (f (μ x:S)=1 ∧ f (μ y:S)≠1 ∧ τ x=1 ∧ τ y=0)) := by
  have ne := residue_nontrivial f μ ell e x y c1 stat
  have piv := pivot f μ x y gen ne
  obtain ⟨s,hs⟩ := ne
  let τ₀ := disp ell s
  have co : IsCocycle μ τ₀ := disp_co μ ell e s
  have unit (g : G) (hg : f (μ g:S)≠1) : IsUnit (1-(μ g:S)) := by
    apply lifts
    rw [map_sub,map_one]
    exact sub_ne_zero.mpr (Ne.symm hg)
  have Cu : IsUnit (τ₀ (portC x y)) := by
    change IsUnit (disp ell s ((⟨portC x y,layer_c x y⟩ : D G) : G))
    rw [disp_derived μ ell e,c1,mul_one]
    exact unit s hs
  by_cases hx : f (μ x:S)=1
  · have hy := piv.resolve_left (not_not_intro hx)
    have cyc : portC y x=(portC x y)⁻¹ := by
      simp only [portC,commutatorElement_inv]
    have cy : IsUnit (τ₀ (portC y x)) := by
      have H := co.2 (portC x y) (portC y x)
      rw [cyc,mul_inv_cancel,co.1] at H
      rw [←cyc] at H
      have h' : (μ (portC x y):S)*τ₀ (portC y x) = -τ₀ (portC x y) := by
        linear_combination -H
      apply isUnit_of_mul_isUnit_right (x:=(μ (portC x y):S))
      rw [h']
      exact Cu.neg
    obtain ⟨τ,hτ,zy,zx⟩ := normalized co y x (unit y hy) cy
    exact ⟨τ,hτ,Or.inr ⟨hx,hy,zx,zy⟩⟩
  · obtain ⟨τ,hτ,zx,zy⟩ := normalized co x y (unit x hx) Cu
    exact ⟨τ,hτ,Or.inl ⟨hx,zx,zy⟩⟩

end RibbonP11
#print axioms RibbonP11.normalize_residue_model
