import RibbonOddResidue

namespace RibbonOdd
open RibbonP11 HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine
universe u
variable {G : Type u} [Group G] [Finite G]

set_option maxHeartbeats 1000000

/-- If no cycle can be found in this stationary group, every active prime
has a canonical bad chart and its mod-p derived quotient is cyclic. -/
theorem active_prime {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad)
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (stat : D G=LS G 2) (ng : ¬Good x y)
    (p : ℕ) [Fact p.Prime] (nz : Nontrivial (PGroup G p)) :
    IsCyclic (PGroup G p) ∧ PrimeBad p ∧
      ∃ (μ : G→*(ZMod p)ˣ) (τ : G→ZMod p),
        RibbonP11.IsCocycle μ τ ∧ Normalized (RingHom.id (ZMod p)) x y μ τ ∧ Bad (Label p μ x y) := by
  letI : Nontrivial (PV G p) := nz
  letI : Finite (PV G p) := Finite.of_surjective (fun d : D G => Additive.ofMul (pπ p d)) (pπ_surj p)
  obtain ⟨I,e,ell,onto,_,c1,eq⟩ := prime_model p x y gen
  let S := PA G p ⧸ I
  letI : Nontrivial S := e.injective.nontrivial
  letI : Finite S := Finite.of_surjective e e.surjective
  let μ := ((Ideal.Quotient.mk I).toMonoidHom.comp (gIn p)).toHomUnits
  have all := residue_bad check d2 x y gen odd stat ng p μ ell onto eq c1
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (fun _ => rfl)
  obtain ⟨L,maxL⟩ := Ideal.exists_maximal S
  obtain ⟨f,hf,hp,b⟩ := all L maxL
  obtain ⟨τ,co,norm⟩ := standard_chart p f.toRingHom x y gen stat μ ell eq c1
  refine ⟨?_,hp,muMap μ f.toRingHom,τ,co,norm,b⟩
  by_cases uniq : ∀ A : Ideal S, A.IsMaximal → A=L
  · have uk : ∀ A : Ideal S, A.IsMaximal → A=RingHom.ker f.toRingHom :=
      fun A h => (uniq A h).trans hf.symm
    rcases local_field_or_jet (K:=ZMod p) (S:=S) f uk with inject | ⟨δ,der,surj⟩
    · let v : PGroup G p→*Multiplicative (ZMod p) :=
        (f.toRingHom.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom).toMultiplicative
      exact isCyclic_of_injective v (inject.comp e.injective)
    · let ψ := jetAlg f δ der
      let cnst : S→ₐ[ZMod p]J p := (Algebra.ofId (ZMod p) (J p)).comp f
      have tangent : δ (μ x:S)≠0 ∨ δ (μ y:S)≠0 := by
        by_contra! z
        have E : ψ=cnst := quotient_hom_ext p x y gen I ψ cnst
          (TrivSqZeroExt.ext rfl z.1) (TrivSqZeroExt.ext rfl z.2)
        obtain ⟨a,ha⟩ := surj (0,1)
        have h : (ψ a).snd=1 := congrArg Prod.snd ha
        rw [E] at h
        exact zero_ne_one h
      obtain ⟨σ,c,n⟩ := normalize_residue_model f.toRingHom
        (fun _ => unique_max_units _ uk) μ ell eq x y gen c1 stat
      have C := map_cocycle ψ.toRingHom μ σ c
      let γ := (Units.map ψ.toRingHom.toMonoidHom).comp μ
      have N : Normalized (TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (ZMod p)).toRingHom
          x y γ (ψ ∘ σ) := by
        rcases n with ⟨a,tx,ty⟩|⟨a,b,tx,ty⟩
        · exact Or.inl ⟨a,by change ψ (σ x)=0; rw [tx,map_zero],
            by change ψ (σ y)=1; rw [ty,map_one]⟩
        · exact Or.inr ⟨a,b,by change ψ (σ x)=1; rw [tx,map_one],
            by change ψ (σ y)=0; rw [ty,map_zero]⟩
      exact False.elim (ng (jets d2 x y p hp γ (ψ∘σ) odd C N b tangent))
  · push_neg at uniq
    obtain ⟨L',maxL',ne⟩ := uniq
    obtain ⟨g,hg,hq,b'⟩ := all L' maxL'
    obtain ⟨σ,c',n'⟩ := standard_chart p g.toRingHom x y gen stat μ ell eq c1
    have distinctLabel : Label p (muMap μ f.toRingHom) x y ≠ Label p (muMap μ g.toRingHom) x y := by
      intro E
      have vX : (f (μ x:S)).val=(g (μ x:S)).val := congrArg (fun t : Triple => t.2.1) E
      have vY : (f (μ y:S)).val=(g (μ y:S)).val := congrArg (fun t : Triple => t.2.2) E
      have X := ZMod.val_injective p vX
      have Y := ZMod.val_injective p vY
      have h : f=g := quotient_hom_ext p x y gen I f g X Y
      exact ne (hg.symm.trans (h ▸ hf))
    exact False.elim (ng (pairs d2 x y p p hp hq (muMap μ f.toRingHom) (muMap μ g.toRingHom)
      τ σ odd co c' norm n' b b' distinctLabel))

end RibbonOdd
#print axioms RibbonOdd.active_prime
