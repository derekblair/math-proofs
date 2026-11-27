import RibbonD3DerivedNoThreeActivePrime
import RibbonD3DerivedNoThreeNonstationary
import RibbonDerived3Family

namespace RibbonD3DerivedNoThree
open RibbonP11 HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine RibbonClass4Fallback RibbonDerived3
open RibbonOdd (Label)
universe u
variable {G : Type u} [Group G] [Finite G]

theorem stationary_bound {Bad : RibbonD3Odd.Triple→Prop} (no3 : GoodDerived G) (check : RibbonD3Odd.FieldCover.{u,u} Bad)
    (pairs : RibbonD3Odd.PairCover.{u} Bad) (jets : RibbonD3Odd.JetCover.{u} Bad) (metab : MetaCover.{u})
    (dnil : DLS G 3=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) (hc : portC x y∈LS G 2) : RibbonD3Odd.WideGood x y := by
  by_contra no
  have stat := RibbonAffine.stationary x y gen hc
  let A := Abelianization (D G)
  letI : Finite A := Finite.of_surjective (Abelianization.of : D G→*A)
    (QuotientGroup.mk'_surjective (commutator (D G)))
  have cyclicA : IsCyclic A := by
    by_cases one : Nat.card A=1
    · letI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp one).1
      infer_instance
    · obtain ⟨p,hp,pA⟩ := Nat.exists_prime_and_dvd one
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨cyc,hP,μ,τ,co,norm,bad⟩ := active_prime no3 check pairs jets dnil x y gen odd stat no p
        (prime_mod_nontrivial p pA)
      have only (q : ℕ) (hq : q.Prime) (qA : q∣Nat.card A) : q=p := by
        by_contra distinct
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨_,hQ,ν,σ,co',norm',bad'⟩ := active_prime no3 check pairs jets dnil x y gen odd stat no q
          (prime_mod_nontrivial q qA)
        have hlabel : Label p μ x y ≠ Label q ν x y := by
          intro e
          exact distinct (congrArg Prod.fst e).symm
        exact no (pairs dnil x y p q hP hQ μ ν τ σ odd co co' norm norm' bad bad' hlabel)
      letI : IsCyclic (PGroup G p) := cyc
      exact cyclic_of_single_prime p only
  letI : IsCyclic A := cyclicA
  have cyc : IsCyclic (D G) := cyclic_of_abelianization ⟨3,RibbonD3Stationary.derived_internal 3 dnil⟩
  letI : IsCyclic (D G) := cyc
  letI : CommGroup (D G) := IsCyclic.commGroup
  have m : RibbonMeta.Meta G := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : D G) (⟨b,hb⟩ : D G))
  exact no (Or.inl (RibbonD3Stationary.widen (metab m x y odd hx hy)))

/-- Ambient-non-nilpotent class-three-derived bound, conditional on the
concrete chart certificates. -/
theorem from_covers {Bad : RibbonD3Odd.Triple→Prop} (no3 : GoodDerived G) (check : RibbonD3Odd.FieldCover.{u,u} Bad)
    (pairs : RibbonD3Odd.PairCover.{u} Bad) (jets : RibbonD3Odd.JetCover.{u} Bad) (metab : MetaCover.{u})
    (dnil : DLS G 3=⊥) (x y : G) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) : RibbonD3Odd.WideGood x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  have d := RibbonDerived3.inherited S dnil
  have gen := pair_generates x y
  have od := Odd.of_dvd_nat odd dvd
  have ns := inherited no3 S
  have H : RibbonD3Odd.WideGood (leftPort x y) (rightPort x y) := by
    by_cases h : portC (leftPort x y) (rightPort x y) ∈ LS S 2
    · exact stationary_bound ns check pairs jets metab d _ _ gen od hx' hy' h
    · exact nonstationary ns d _ _ gen od hx' hy' h
  rcases H with (h|h|h|h|h|h)|h
  · exact Or.inl (Or.inl (pair_lift x y 4 h))
  · exact Or.inl (Or.inr (Or.inl (pair_lift x y 8 h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (pair_lift x y 16 h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h))))))
  · exact Or.inr (pair_lift x y 256 h)

end RibbonD3DerivedNoThree
#print axioms RibbonD3DerivedNoThree.stationary_bound
#print axioms RibbonD3DerivedNoThree.from_covers
