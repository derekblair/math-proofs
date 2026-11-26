import RibbonOrder3Nakayama
import RibbonP11FieldRun

namespace RibbonOrder3
open RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
universe u
variable {G : Type u} [Group G]

/-- A nontrivial finite residue action allows a deterministic normalization:
use x as origin if its multiplier is nontrivial, otherwise use y. -/
theorem normalize_character {K : Type*} [Field K]
    (x y : G) (gen : Generates x y)
    (μ : G→*Kˣ) (l : D G→*Multiplicative K)
    (eq : RibbonP11.Equivariant μ l)
    (c1 : Multiplicative.toAdd (l ⟨portC x y,layer_c x y⟩)=1)
    (act : ∃ s, μ s≠1) :
    ∃ τ : G→K, RibbonP11.IsCocycle μ τ ∧
      RibbonP11.Normalized (RingHom.id K) x y μ τ := by
  have pv : μ x≠1 ∨ μ y≠1 := by
    by_contra! bad
    have incl : Subgroup.closure ({x,y}:Set G) ≤ μ.ker := by
      apply (Subgroup.closure_le _).mpr
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl|rfl
      · exact bad.1
      · exact bad.2
    change Subgroup.closure ({x,y}:Set G)=⊤ at gen
    rw [gen] at incl
    obtain ⟨s,hs⟩ := act
    exact hs (incl (Subgroup.mem_top s))
  obtain ⟨s,hs⟩ := act
  let τ₀ := RibbonP11.disp l s
  have co : RibbonP11.IsCocycle μ τ₀ := RibbonP11.disp_co μ l eq s
  have unit (g : G) (h : μ g≠1) : IsUnit (1-(μ g:K)) := by
    apply isUnit_iff_ne_zero.mpr
    intro z
    exact h (Units.ext (sub_eq_zero.mp z).symm)
  have cu : IsUnit (τ₀ (portC x y)) := by
    change IsUnit (RibbonP11.disp l s ((⟨portC x y,layer_c x y⟩ : D G) : G))
    rw [RibbonP11.disp_derived μ l eq,c1,mul_one]
    exact unit s hs
  have same {g : G} : (μ g:K)=1 ↔ μ g=1 := by
    constructor
    · intro h
      apply Units.ext
      exact h
    · intro h
      rw [h]
      rfl
  by_cases hx : μ x=1
  · have hy := pv.resolve_left (not_not_intro hx)
    have flip : portC y x=(portC x y)⁻¹ := by simp only [portC,commutatorElement_inv]
    have cv : IsUnit (τ₀ (portC y x)) := by
      have H := co.2 (portC x y) (portC y x)
      rw [flip,mul_inv_cancel,co.1,←flip] at H
      have E : (μ (portC x y):K)*τ₀ (portC y x) = -τ₀ (portC x y) := by
        linear_combination -H
      apply isUnit_of_mul_isUnit_right (x:=(μ (portC x y):K))
      rw [E]
      exact cu.neg
    obtain ⟨τ,tCo,zy,zx⟩ := RibbonP11.normalized co y x (unit y hy) cv
    exact ⟨τ,tCo,Or.inr ⟨same.mpr hx,fun h => hy (same.mp h),zx,zy⟩⟩
  · obtain ⟨τ,tCo,zx,zy⟩ := RibbonP11.normalized co x y (unit x hx) cu
    exact ⟨τ,tCo,Or.inl ⟨fun h => hx (same.mp h),zx,zy⟩⟩

/-- A stable nonzero third layer in a class-two-derived group yields a
nontrivial simple affine residue. The coefficient field need not have
characteristic 3, even when the class-two commutator has order 3. -/
theorem stable_third_affine_of_visible [Finite G]
    (x y : G) (gen : Generates x y) (odd : Odd (Nat.card G))
    (st : LS G 2=LS G 3)
    (hn : ¬LS G 2≤(commutator (D G)).map (D G).subtype) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (μ : G→*Kˣ) (τ : G→K),
      (2:K)≠0 ∧ RibbonP11.IsCocycle μ τ ∧
      RibbonP11.Normalized (RingHom.id K) x y μ τ ∧
      (μ x)^(Nat.card G)=1 ∧ (μ y)^(Nat.card G)=1 := by
  obtain ⟨I,l,μ,lS,ker,c1,eq⟩ := integral_model x y gen
  let S := A G ⧸ I
  letI : Finite S := Finite.of_surjective l lS
  have hN : ∃ d : D G, d.val∈LS G 2 ∧ l d≠1 := by
    obtain ⟨d,hd,hbad⟩ := SetLike.not_le_iff_exists.mp hn
    let e : D G := ⟨d,Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 1≤2) hd⟩
    refine ⟨e,hd,fun h => hbad ?_⟩
    exact Subgroup.mem_map_of_mem _ ((ker e).mp h)
  obtain ⟨L,lm,s,hs⟩ := nontrivial_residue μ l eq st hN
  letI : L.IsMaximal := lm
  let K := S ⧸ L
  letI : Field K := Ideal.Quotient.field L
  let f := Ideal.Quotient.mk L
  letI : Finite K := Finite.of_surjective f Ideal.Quotient.mk_surjective
  let ρ := (Units.map f.toMonoidHom).comp μ
  let ell := f.toAddMonoidHom.toMultiplicative.comp l
  have c : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1 := by
    change f (Multiplicative.toAdd (l ⟨portC x y,layer_c x y⟩))=1
    rw [c1,map_one]
  have E := RibbonP11.map_equivariant f μ l eq
  have hs' : ρ s≠1 := fun one => hs (congrArg (fun a : Kˣ => (a:K)) one)
  obtain ⟨τ,co,n⟩ := normalize_character x y gen ρ ell E c ⟨s,hs'⟩
  have powers (g : G) : (ρ g)^(Nat.card G)=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_map_dvd ρ g) (orderOf_dvd_natCard g))
  have two := RibbonP11.odd_field_two ell (Ideal.Quotient.mk_surjective.comp lS) odd
  exact ⟨K,inferInstance,inferInstance,ρ,τ,two,co,n,powers x,powers y⟩

end RibbonOrder3
#print axioms RibbonOrder3.stable_third_affine_of_visible
