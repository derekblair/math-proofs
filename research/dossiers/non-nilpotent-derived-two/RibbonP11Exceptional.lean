import RibbonP11FieldGen
import RibbonP11PrimeDetect

namespace RibbonP11
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine
universe u
variable {G : Type u} [Group G] [Finite G]

set_option maxHeartbeats 1000000

private theorem prime_eq11 (p : ℕ) (hp : Nat.Prime p) {K : Type*} [Field K]
    (f : ZMod p→+*K) (e : F→+*K) : p=11 := by
  have z : (p:K)=0 := by
    rw [←map_natCast f,ZMod.natCast_self,map_zero]
  have w : (p:F)=0 := e.injective (by rw [map_natCast,map_zero,z])
  have d := (CharP.cast_eq_zero_iff F 11 p).mp w
  exact ((Nat.dvd_prime hp).mp d).resolve_left (by decide) |>.symm

/-- Without a successful single-field chart, every nonzero prime model
is necessarily at 11. -/
theorem no_other_prime {Bad : F×F→Prop} (check : FieldCover.{u,u} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (stat : D G=LS G 2) (ng : ¬Good x y)
    (p : ℕ) (hp : Nat.Prime p) (nz : Nontrivial (PGroup G p)) : p=11 := by
  obtain ⟨I,e,ell,onto,_,c1,eq⟩ := prime_model p x y gen
  let S := PA G p ⧸ I
  letI : Nontrivial (PV G p) := nz
  letI : Finite (PV G p) := Finite.of_surjective (fun d : D G => Additive.ofMul (pπ p d)) (pπ_surj p)
  letI : Nontrivial S := e.injective.nontrivial
  letI : Finite S := Finite.of_surjective e e.surjective
  obtain ⟨L,mL⟩ := Ideal.exists_maximal S
  letI : L.IsMaximal := mL
  let K := S ⧸ L
  letI : Field K := Ideal.Quotient.field L
  let f := Ideal.Quotient.mk L
  letI : Finite K := Finite.of_surjective f Ideal.Quotient.mk_surjective
  let μ := ((Ideal.Quotient.mk I).toMonoidHom.comp (gIn p)).toHomUnits
  rcases field_run check d2 x y gen odd no3 stat f Ideal.Quotient.mk_surjective μ ell onto eq c1
      with h | ⟨_,e',_,_,_,_,_,_,_⟩
  · exact False.elim (ng h)
  · exact prime_eq11 p hp (f.comp (algebraMap (ZMod p) S)) e'

/-- If no cycle is available, all maximal quotients of the mod-11 model
are canonically the prime field and their port pairs are certified bad. -/
private theorem residue_exists {Bad : F×F→Prop} (check : FieldCover.{u,u} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (stat : D G=LS G 2) (ng : ¬Good x y)
    {S : Type u} [CommRing S] [Finite S] [Algebra F S] (μ : G→*Sˣ)
    (ell : D G→*Multiplicative S) (onto : Function.Surjective ell)
    (eq : Equivariant μ ell) (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1)
    (hQ : PA G 11→+*S) (Qsurj : Function.Surjective hQ)
    (qμ : ∀ g, hQ (gIn 11 g)=(μ g:S))
    (L : Ideal S) (mL : L.IsMaximal) :
    ∃ f : S→ₐ[F]F, RingHom.ker f.toRingHom=L := by
  letI : L.IsMaximal := mL
  let K := S ⧸ L
  letI : Field K := Ideal.Quotient.field L
  let f := Ideal.Quotient.mk L
  letI : Finite K := Finite.of_surjective f Ideal.Quotient.mk_surjective
  obtain ⟨_,e,a,b,_,_,hA,hB,_⟩ := (field_run check d2 x y gen odd no3 stat f Ideal.Quotient.mk_surjective
    μ ell onto eq c1).resolve_left ng
  have hs : Function.Surjective e := prime11_residue_generated x y gen (f.comp hQ)
    (Ideal.Quotient.mk_surjective.comp Qsurj) e a b
    (by change e a=f (hQ (gIn 11 x)); rw [qμ]; exact hA)
    (by change e b=f (hQ (gIn 11 y)); rw [qμ]; exact hB)
  let E : F ≃+* K := RingEquiv.ofBijective e ⟨e.injective,hs⟩
  obtain ⟨g,hg⟩ := residue_alg11 (E.symm.toRingHom.comp f)
  refine ⟨g,?_⟩
  ext a
  change g.toRingHom a=0 ↔ a∈L
  rw [hg]
  change E.symm (f a)=0 ↔ a∈L
  rw [←E.symm.map_zero,E.symm.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem std_field_run {Bad : F×F→Prop} (check : FieldCover.{u,0} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (stat : D G=LS G 2) (ng : ¬Good x y)
    {S : Type u} [CommRing S] [Algebra F S] (μ : G→*Sˣ)
    (ell : D G→*Multiplicative S) (onto : Function.Surjective ell)
    (eq : Equivariant μ ell) (c1 : Multiplicative.toAdd (ell ⟨portC x y,layer_c x y⟩)=1)
    (f : S→ₐ[F]F) :
    ∃ τ : G→F, IsCocycle (muMap μ f.toRingHom) τ ∧
      Normalized (RingHom.id F) x y (muMap μ f.toRingHom) τ ∧ Bad (f (μ x:S),f (μ y:S)) := by
  have surj : Function.Surjective f := fun a => ⟨algebraMap F S a, f.commutes a⟩
  obtain ⟨τ,e,a,b,c,n,hA,hB,bad⟩ := (field_run check d2 x y gen odd no3 stat f.toRingHom surj
    μ ell onto eq c1).resolve_left ng
  have E : e=RingHom.id F := RingHom.ext_zmod _ _
  rw [E] at hA hB
  exact ⟨τ,c,n,hA ▸ hB ▸ bad⟩

/-- At p=11 the residue-pair and dual-word checks force the mod-11
abelianization to be cyclic if there is no short cycle. -/
theorem mod11_cyclic {Bad : F×F→Prop} (check : FieldCover.{u,u} Bad)
    (checkSmall : FieldCover.{u,0} Bad) (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (stat : D G=LS G 2) (ng : ¬Good x y) :
    IsCyclic (PGroup G 11) := by
  by_cases nV : Nontrivial (PGroup G 11)
  · letI : Nontrivial (PV G 11) := nV
    letI : Finite (PV G 11) := Finite.of_surjective (fun d : D G => Additive.ofMul (pπ 11 d)) (pπ_surj 11)
    obtain ⟨I,e,ell,onto,_,c1,eq⟩ := prime_model 11 x y gen
    let S := PA G 11 ⧸ I
    letI : Nontrivial S := e.injective.nontrivial
    letI : Finite S := Finite.of_surjective e e.surjective
    let μ := ((Ideal.Quotient.mk I).toMonoidHom.comp (gIn 11)).toHomUnits
    have all := residue_exists check d2 x y gen odd no3 stat ng μ ell onto eq c1
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (fun _ => rfl)
    obtain ⟨L,maxL⟩ := Ideal.exists_maximal S
    obtain ⟨f,hf⟩ := all L maxL
    by_cases uniq : ∀ A : Ideal S, A.IsMaximal → A=L
    · have uk : ∀ A : Ideal S, A.IsMaximal → A=RingHom.ker f.toRingHom :=
        fun A h => (uniq A h).trans hf.symm
      rcases local_field_or_jet (K:=F) (S:=S) f uk with inject | ⟨δ,der,surj⟩
      · let v : PGroup G 11→*Multiplicative F :=
          (f.toRingHom.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom).toMultiplicative
        exact isCyclic_of_injective v (inject.comp e.injective)
      · let ψ := jetAlg f δ der
        let cnst : S→ₐ[F]J := (Algebra.ofId F J).comp f
        have tangent : δ (μ x:S)≠0 ∨ δ (μ y:S)≠0 := by
          by_contra! z
          have E : ψ=cnst := quotient_hom_ext 11 x y gen I ψ cnst
            (TrivSqZeroExt.ext rfl z.1) (TrivSqZeroExt.ext rfl z.2)
          obtain ⟨a,ha⟩ := surj (0,1)
          have h : (ψ a).snd=1 := congrArg Prod.snd ha
          rw [E] at h
          exact zero_ne_one h
        obtain ⟨_,_,_,b⟩ := std_field_run checkSmall d2 x y gen odd no3 stat ng μ ell onto eq c1 f
        obtain ⟨τ,c,n⟩ := normalize_residue_model f.toRingHom
          (fun _ => unique_max_units _ uk) μ ell eq x y gen c1 stat
        have co := map_cocycle ψ.toRingHom μ τ c
        let γ := (Units.map ψ.toRingHom.toMonoidHom).comp μ
        have normal : Normalized (TrivSqZeroExt.fstHom F F F).toRingHom x y γ (ψ ∘ τ) := by
          rcases n with ⟨a,tx,ty⟩|⟨a,b,tx,ty⟩
          · exact Or.inl ⟨a,by change ψ (τ x)=0; rw [tx,map_zero],
              by change ψ (τ y)=1; rw [ty,map_one]⟩
          · exact Or.inr ⟨a,b,by change ψ (τ x)=1; rw [tx,map_one],
              by change ψ (τ y)=0; rw [ty,map_zero]⟩
        exact False.elim (ng (jets d2 x y γ (ψ∘τ) odd co normal b tangent))
    · push_neg at uniq
      obtain ⟨L',maxL',ne⟩ := uniq
      obtain ⟨g,hg⟩ := all L' maxL'
      obtain ⟨τ,c,n,b⟩ := std_field_run checkSmall d2 x y gen odd no3 stat ng μ ell onto eq c1 f
      obtain ⟨σ,c',n',b'⟩ := std_field_run checkSmall d2 x y gen odd no3 stat ng μ ell onto eq c1 g
      have distinct : (f (μ x:S),f (μ y:S)) ≠ (g (μ x:S),g (μ y:S)) := by
        intro E
        have h : f=g := quotient_hom_ext 11 x y gen I f g (congrArg Prod.fst E) (congrArg Prod.snd E)
        exact ne (hg.symm.trans (h ▸ hf))
      exact False.elim (ng (pairs d2 x y (muMap μ f.toRingHom) (muMap μ g.toRingHom) τ σ
        odd c c' n n' b b' distinct))
  · letI : Subsingleton (PGroup G 11) := not_nontrivial_iff_subsingleton.mp nV
    infer_instance

end RibbonP11
#print axioms RibbonP11.no_other_prime
#print axioms RibbonP11.mod11_cyclic
