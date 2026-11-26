import RibbonP11Interfaces
import Mathlib.Algebra.Algebra.ZMod

namespace RibbonP11
open RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports
universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {S : Type v} {K : Type w} [CommRing S] [Field K] [Finite K]

theorem odd_field_two [Finite K] (ell : D G→*Multiplicative K)
    (onto : Function.Surjective ell) (odd : Odd (Nat.card G)) : (2:K)≠0 := by
  have fieldOdd : Odd (Nat.card (Multiplicative K)) :=
    Odd.of_dvd_nat odd (dvd_trans (Subgroup.card_dvd_of_surjective ell onto) (D G).card_subgroup_dvd_card)
  intro z
  have I : (1 : Multiplicative K) ≠ Multiplicative.ofAdd 1 :=
    fun v => one_ne_zero (congrArg Multiplicative.toAdd v).symm
  have h2 : (Multiplicative.ofAdd (1:K))^2=1 := by
    rw [pow_two]
    change (1:K)+1=0
    simpa only [one_add_one_eq_two] using z
  exact HaarClass3Odd.odd_no_involution (G:=Multiplicative K) fieldOdd I.symm h2

abbrev muMap (μ : G→*Sˣ) (f : S→+*K) : G→*Kˣ :=
  (Units.map f.toMonoidHom).comp μ

/-- Normalized and possibly bad canonical residue coordinates in a
single residue field; no subsequent group structure is assumed here. -/
theorem field_run {S : Type v} {K : Type w} [CommRing S] [Field K] [Finite K]
    {Bad : F×F→Prop} (check : FieldCover.{u,w} Bad) (d2 : RibbonDerivedTwo.D2 G)
    (x y : G) (gen : Generates x y) (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (stat : D G=LS G 2)
    (f : S→+*K) (fSurj : Function.Surjective f)
    (μ : G→*Sˣ) (ell : D G→*Multiplicative S) (onto : Function.Surjective ell)
    (eq : Equivariant μ ell) (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1) :
    Good x y ∨ ∃ (τ : G→K) (e : F→+*K) (a b : F), IsCocycle (muMap μ f) τ ∧
      Normalized (RingHom.id K) x y (muMap μ f) τ ∧
      e a=f (μ x:S) ∧ e b=f (μ y:S) ∧ Bad (a,b) := by
  let L := f.toAddMonoidHom.toMultiplicative.comp ell
  have LS : Function.Surjective L := fSurj.comp onto
  have EQ := map_equivariant f μ ell eq
  have C : Multiplicative.toAdd (L ⟨portC x y,layer_c x y⟩)=1 := by
    change f (Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩))=1
    rw [c1,map_one]
  obtain ⟨τ,co,N⟩ := normalize_residue_model (RingHom.id K)
    (fun r nr => isUnit_iff_ne_zero.mpr nr) (muMap μ f) L EQ x y gen C stat
  rcases check d2 x y (muMap μ f) τ (odd_field_two L LS odd) odd no3 co N with h | ⟨e,a,b,hA,hB,bad⟩
  · exact Or.inl h
  · exact Or.inr ⟨τ,e,a,b,co,N,hA,hB,bad⟩

theorem residue_alg11 {S : Type u} [CommRing S] [Algebra F S]
    (f : S→+*F) : ∃ g : S→ₐ[F] F, g.toRingHom=f := by
  let g : S→ₐ[F] F :=
    { toRingHom := f
      commutes' := fun a => DFunLike.congr_fun (RingHom.ext_zmod
        (f.comp (algebraMap F S)) (algebraMap F F)) a }
  exact ⟨g,rfl⟩

theorem bad_self {Bad : F×F→Prop} {a b : F} (e : F ≃+* F)
    (h : Bad (e a,e b)) : Bad (a,b) := by
  have EE : e.toRingHom = RingHom.id F := RingHom.ext_zmod _ _
  have ea : e a=a := DFunLike.congr_fun EE a
  have eb : e b=b := DFunLike.congr_fun EE b
  rwa [ea,eb] at h

end RibbonP11
#print axioms RibbonP11.field_run
