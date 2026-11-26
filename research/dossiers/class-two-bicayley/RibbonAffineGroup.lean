import RibbonAffineScalar
import RibbonAffineNormalize
import RibbonMetaDrop
import Mathlib.FieldTheory.Finite.Basic

namespace RibbonAffine
open HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
universe u
variable {G : Type u} [Group G]
variable {K : Type*} [Field K]

set_option maxHeartbeats 1000000

private theorem derived_commGroup (m : RibbonMeta.Meta G) :
    IsMulCommutative (D G) := by
  rw [isMulCommutative_iff]
  intro a b
  exact Subtype.ext (m a.val a.property b.val b.property).eq

/-- If c is invisible in the class-two quotient, the series stabilizes
at the entire derived subgroup. No nilpotence is assumed here. -/
theorem stationary (x y : G) (gen : Generates x y)
    (hc : portC x y∈LS G 2) : D G=LS G 2 := by
  let S := LS G 2
  let φ := QuotientGroup.mk' S
  have g := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have r : Commute (φ x) (φ y) := by
    have C : φ (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
    change φ x*φ y=φ y*φ x
    simpa only [map_mul,C,mul_one] using congrArg φ (ports_xy x y)
  let : IsMulCommutative (G ⧸ S) := gen_comm _ _ g r
  have zero : LS (G ⧸ S) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot (G ⧸ S))
  have h := map_ls φ (QuotientGroup.mk'_surjective S) 1
  rw [zero,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at h
  exact le_antisymm h (Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 1≤2))

private theorem scalar_derived [Finite G] (m : RibbonMeta.Meta G) (nt : Nontrivial (D G)) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K)
      (μ : G →* Kˣ) (ell : D G →* Multiplicative K),
      Function.Surjective ell ∧ Equivariant μ ell := by
  letI := nt
  letI : CommGroup (D G) := { (inferInstance : Group (D G)) with
    mul_comm := isMulCommutative_iff.mp (derived_commGroup m) }
  let ρ : G →* Module.End ℤ (Additive (D G)) :=
    { toFun := fun g => ((MulAut.conjNormal g).toAdditive.toAddMonoidHom).toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro d
        change Additive.ofMul (MulAut.conjNormal (1:G) d.toMul) = d
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro d
        change Additive.ofMul (MulAut.conjNormal (g*h) d.toMul) =
          Additive.ofMul (MulAut.conjNormal g (MulAut.conjNormal h d.toMul))
        rw [map_mul]
        rfl }
  have ker : commutator G ≤ ρ.ker := by
    intro g hg
    have h : g∈D G := hg
    change ρ g=1
    apply LinearMap.ext
    intro d
    change Additive.ofMul (MulAut.conjNormal g d.toMul) = Additive.ofMul d.toMul
    apply congrArg Additive.ofMul
    apply Subtype.ext
    rw [MulAut.conjNormal_apply,(m g h d.toMul.val d.toMul.property).eq,mul_inv_cancel_right]
  let abρ : Abelianization G →* Module.End ℤ (Additive (D G)) :=
    QuotientGroup.lift (commutator G) ρ ker
  obtain ⟨K,fK,finit,α,ell,surj,action⟩ := scalar_quotient abρ
  let μ := α.comp Abelianization.of
  let L : D G →* Multiplicative K := ell.toMultiplicative
  refine ⟨K,fK,finit,μ,L,surj,fun g d => ?_⟩
  exact action (Abelianization.of g) (Additive.ofMul d)

private def kernel_ambient (ell : D G →* Multiplicative K) : Subgroup G :=
  ell.ker.map (D G).subtype

private theorem kernel_normal {μ : G →* Kˣ} {ell : D G →* Multiplicative K}
    (e : Equivariant μ ell) : (kernel_ambient ell).Normal := by
  constructor
  intro a ha g
  obtain ⟨d,hd,rfl⟩ := ha
  refine ⟨MulAut.conjNormal g d,?_,MulAut.conjNormal_apply g d⟩
  change ell (MulAut.conjNormal g d)=1
  change ell d=1 at hd
  change Multiplicative.toAdd (ell (MulAut.conjNormal g d))=0
  rw [e,hd]
  exact mul_zero _

private theorem kernel_proper (ell : D G →* Multiplicative K) (surj : Function.Surjective ell) :
    kernel_ambient ell < D G := by
  apply lt_of_le_of_ne
  · rintro a ⟨d,hd,rfl⟩
    exact d.property
  · intro H
    obtain ⟨d,hd⟩ := surj (Multiplicative.ofAdd (1:K))
    have hz : d.val ∈ kernel_ambient ell := H.symm ▸ d.property
    obtain ⟨z,hz,e⟩ := hz
    have ed : z=d := Subtype.ext e
    subst z
    change ell d=1 at hz
    rw [hd] at hz
    exact one_ne_zero (congrArg Multiplicative.toAdd hz)

private theorem scalar_nontrivial {μ : G →* Kˣ} {ell : D G →* Multiplicative K}
    (e : Equivariant μ ell) (surj : Function.Surjective ell) (h : D G=LS G 2) :
    ∃ s : G, μ s≠1 := by
  by_contra! no
  have all : LS G 2 ≤ kernel_ambient ell := by
    change ⁅LS G 1,(⊤ : Subgroup G)⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro d hd s _
    refine ⟨cAt d s,?_,rfl⟩
    change displacement ell s d=0
    rw [displacement_derived μ ell e s ⟨d,hd⟩,no s]
    simp
  exact (not_le_of_gt (kernel_proper ell surj)) (h ▸ all)

private theorem detects {μ : G →* Kˣ} {ell : D G →* Multiplicative K}
    (e : Equivariant μ ell) (surj : Function.Surjective ell) (x y : G)
    (gen : Generates x y) : ell ⟨portC x y,layer_c x y⟩ ≠ 1 := by
  intro z
  letI := kernel_normal e
  apply survives_in_normal_quotient x y gen (kernel_ambient ell) (kernel_proper ell surj)
  exact ⟨⟨portC x y,layer_c x y⟩,z,rfl⟩

private theorem one_multiplier {μ : G →* Kˣ} (x y : G) (gen : Generates x y)
    (nontriv : ∃ s, μ s≠1) : μ x≠1 ∨ μ y≠1 := by
  by_contra! no
  have h : Subgroup.closure ({x,y} : Set G) ≤ μ.ker := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact no.1
    · exact no.2
  change Subgroup.closure ({x,y} : Set G) = ⊤ at gen
  rw [gen] at h
  obtain ⟨s,hs⟩ := nontriv
  exact hs (h (Subgroup.mem_top s))

theorem stationary_affine [Finite G] (m : RibbonMeta.Meta G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (hc : portC x y∈LS G 2) (hn : portC x y≠1) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (μ : G →* Kˣ) (τ : G → K) (n : ℕ),
      (2:K) ≠ 0 ∧ IsCocycle μ τ ∧ Odd n ∧ (μ x)^n=1 ∧ (μ y)^n=1 ∧
      ((μ x≠1 ∧ τ x=0 ∧ τ y=1) ∨ (μ y≠1 ∧ τ y=0 ∧ τ x=1)) := by
  have nt : Nontrivial (D G) :=
    ⟨⟨⟨portC x y,layer_c x y⟩,1,fun z => hn (congrArg Subtype.val z)⟩⟩
  obtain ⟨K,field,fin,μ,ell,surj,e⟩ := scalar_derived m nt
  have fieldOdd : Odd (Nat.card (Multiplicative K)) :=
    Odd.of_dvd_nat odd (dvd_trans (Subgroup.card_dvd_of_surjective ell surj) (D G).card_subgroup_dvd_card)
  have two : (2:K)≠0 := by
    intro z
    have I : (1 : Multiplicative K) ≠ Multiplicative.ofAdd 1 :=
      fun v => one_ne_zero (congrArg Multiplicative.toAdd v).symm
    have h2 : (Multiplicative.ofAdd (1:K))^2=1 := by
      rw [pow_two]
      change (1:K)+1=0
      simpa only [one_add_one_eq_two] using z
    have U := HaarClass3Odd.odd_no_involution (G:=Multiplicative K) fieldOdd I.symm
    exact U h2
  have nontriv := scalar_nontrivial e surj (stationary x y gen hc)
  have which := one_multiplier x y gen nontriv
  obtain ⟨s,hs⟩ := nontriv
  let raw := displacement ell s
  have co := displacement_cocycle μ ell e s
  have ca := displacement_detects μ ell e s hs (⟨portC x y,layer_c x y⟩ : D G)
    (detects e surj x y gen)
  have pow (g : G) : (μ g)^(Nat.card G)=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_map_dvd μ g) (orderOf_dvd_natCard g))
  rcases which with hx|hy
  · obtain ⟨τ,coT,z,w⟩ := normalized co x y hx ca
    exact ⟨K,field,fin,μ,τ,Nat.card G,two,coT,odd,pow x,pow y,Or.inl ⟨hx,z,w⟩⟩
  · have sw : Generates y x := by unfold Generates at gen ⊢; rwa [Set.pair_comm]
    have cb := displacement_detects μ ell e s hs (⟨portC y x,layer_c y x⟩ : D G)
      (detects e surj y x sw)
    obtain ⟨τ,coT,z,w⟩ := normalized co y x hy cb
    exact ⟨K,field,fin,μ,τ,Nat.card G,two,coT,odd,pow x,pow y,Or.inr ⟨hy,z,w⟩⟩

end RibbonAffine
#print axioms RibbonAffine.stationary_affine
