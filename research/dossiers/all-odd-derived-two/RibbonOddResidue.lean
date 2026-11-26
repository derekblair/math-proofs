import RibbonOddFieldGen

namespace RibbonOdd
open RibbonP11 RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports
universe u v
variable {G : Type u} [Group G] [Finite G]

set_option maxHeartbeats 1000000

theorem same_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {K : Type v} [Field K]
    (f : ZMod p→+*K) (e : ZMod q→+*K) : p=q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have z : (p:K)=0 := by rw [←map_natCast f,ZMod.natCast_self,map_zero]
  have w : (p:ZMod q)=0 := e.injective (by rw [map_natCast,map_zero,z])
  have d := (CharP.cast_eq_zero_iff (ZMod q) q p).mp w
  exact ((Nat.dvd_prime hp).mp d).resolve_left hq.ne_one |>.symm

/-- Normalize over a chosen prime-field residue map, with no second
application of the arbitrary-field checker. -/
theorem standard_chart (p : ℕ) [Fact p.Prime] {S : Type u} [CommRing S]
    (f : S→+*ZMod p) (x y : G) (gen : Generates x y) (st : D G=LS G 2)
    (μ : G→*Sˣ) (ell : D G→*Multiplicative S) (eq : Equivariant μ ell)
    (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1) :
    ∃ τ : G→ZMod p, RibbonP11.IsCocycle (muMap μ f) τ ∧
      Normalized (RingHom.id (ZMod p)) x y (muMap μ f) τ := by
  let L := f.toAddMonoidHom.toMultiplicative.comp ell
  have EQ := map_equivariant f μ ell eq
  have C : Multiplicative.toAdd (L ⟨portC x y,layer_c x y⟩)=1 := by
    change f (Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩))=1
    rw [c1,map_one]
  exact normalize_residue_model (RingHom.id (ZMod p))
    (fun r nr => isUnit_iff_ne_zero.mpr nr) (muMap μ f) L EQ x y gen C st

/-- Every maximal ideal of a modeled action ring gives one of the canonical
bad prime-field characters if the arbitrary-field checker finds no cycle. -/
theorem residue_bad {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (st : D G=LS G 2) (ng : ¬Good x y)
    (p : ℕ) [Fact p.Prime] {S : Type u} [CommRing S] [Finite S] [Algebra (ZMod p) S]
    (μ : G→*Sˣ) (ell : D G→*Multiplicative S) (onto : Function.Surjective ell)
    (eq : Equivariant μ ell) (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1)
    (q : PA G p→+*S) (Q : Function.Surjective q)
    (qμ : ∀ g, q (gIn p g)=(μ g:S))
    (L : Ideal S) (mL : L.IsMaximal) :
    ∃ f : S→ₐ[ZMod p]ZMod p, RingHom.ker f.toRingHom=L ∧
      PrimeBad p ∧ Bad (p,(f (μ x:S)).val,(f (μ y:S)).val) := by
  letI : L.IsMaximal := mL
  let K := S ⧸ L
  letI : Field K := Ideal.Quotient.field L
  let f := Ideal.Quotient.mk L
  letI : Finite K := Finite.of_surjective f Ideal.Quotient.mk_surjective
  let LL := f.toAddMonoidHom.toMultiplicative.comp ell
  have LS : Function.Surjective LL := Ideal.Quotient.mk_surjective.comp onto
  have EQ := map_equivariant f μ ell eq
  have CC : Multiplicative.toAdd (LL ⟨portC x y,layer_c x y⟩)=1 := by
    change f (Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩))=1
    rw [c1,map_one]
  obtain ⟨τ,c,n⟩ := normalize_residue_model (RingHom.id K)
    (fun r nr => isUnit_iff_ne_zero.mpr nr) (muMap μ f) LL EQ x y gen CC st
  obtain ⟨p',hp',e,a,b,hA,hB,bad⟩ :=
    (check d2 x y (muMap μ f) τ (odd_field_two LL LS odd) odd c n).resolve_left ng
  have P : p=p' := same_prime (p:=p) (q:=p') Fact.out (prime_of_bad hp')
    (f.comp (algebraMap (ZMod p) S)) e
  subst p'
  have ea : e a=f (μ x:S) := hA
  have eb : e b=f (μ y:S) := hB
  have hs : Function.Surjective e := prime_residue_generated p x y gen (f.comp q)
    (Ideal.Quotient.mk_surjective.comp Q) e a b
    (by change e a=f (q (gIn p x)); rw [qμ]; exact ea)
    (by change e b=f (q (gIn p y)); rw [qμ]; exact eb)
  let E : ZMod p ≃+* K := RingEquiv.ofBijective e ⟨e.injective,hs⟩
  let g₀ := E.symm.toRingHom.comp f
  let g : S→ₐ[ZMod p]ZMod p :=
    { toRingHom := g₀
      commutes' := fun k => DFunLike.congr_fun (RingHom.ext_zmod
        (g₀.comp (algebraMap (ZMod p) S)) (algebraMap (ZMod p) (ZMod p))) k }
  refine ⟨g,?_,hp',?_⟩
  · ext z
    change E.symm (f z)=0 ↔ z∈L
    rw [←E.symm.map_zero,E.symm.injective.eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  · have hX : g (μ x:S)=a := by
      change E.symm (f (μ x:S))=a
      rw [←ea]
      exact E.symm_apply_apply a
    have hY : g (μ y:S)=b := by
      change E.symm (f (μ y:S))=b
      rw [←eb]
      exact E.symm_apply_apply b
    rwa [hX,hY]

end RibbonOdd
#print axioms RibbonOdd.residue_bad
