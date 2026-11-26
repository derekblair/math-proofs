import RibbonOddActivePrime
import RibbonOrder3Nonstationary

namespace RibbonOdd
open RibbonP11 HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine RibbonClass4Fallback
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full stationary all-odd group dispatch. The cross-prime pair
certificate prevents two different primes from dividing |D_ab|. -/
theorem stationary_bound {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) (hc : portC x y∈LS G 2) :
    Good x y := by
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
      obtain ⟨cyc,hP,μ,τ,co,norm,bad⟩ := active_prime check pairs jets d2 x y gen odd stat no p
        (prime_mod_nontrivial p pA)
      have only (q : ℕ) (hq : q.Prime) (qA : q∣Nat.card A) : q=p := by
        by_contra distinct
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨_,hQ,ν,σ,co',norm',bad'⟩ := active_prime check pairs jets d2 x y gen odd stat no q
          (prime_mod_nontrivial q qA)
        have hlabel : Label p μ x y ≠ Label q ν x y := by
          intro e
          exact distinct (congrArg Prod.fst e).symm
        exact no (pairs d2 x y p q hP hQ μ ν τ σ odd co co' norm norm' bad bad' hlabel)
      letI : IsCyclic (PGroup G p) := cyc
      exact cyclic_of_single_prime p only
  letI : IsCyclic A := cyclicA
  have cyc : IsCyclic (D G) := cyclic_of_abelianization ⟨2,derived_nil d2⟩
  letI : IsCyclic (D G) := cyc
  letI : CommGroup (D G) := IsCyclic.commGroup
  have m : RibbonMeta.Meta G := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : D G) (⟨b,hb⟩ : D G))
  exact no (metab m x y odd hx hy)

/-- All finite odd groups with class-two derived subgroup, conditional
only on the four concrete word-certificate interfaces and the
already proved metabelian cover. -/
theorem finite_odd_derived2_of_covers {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (mix : RibbonOrder3.MixedOrder3Cover.{u})
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Good x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  have d := RibbonDerivedTwo.subgroup_d2 d2 S
  have gen := pair_generates x y
  have od := Odd.of_dvd_nat odd dvd
  have H : Good (leftPort x y) (rightPort x y) := by
    by_cases h : portC (leftPort x y) (rightPort x y) ∈ LS S 2
    · exact stationary_bound check pairs jets metab d _ _ gen od hx' hy' h
    · exact RibbonOrder3.nonstationary_bound mix d _ _ gen od hx' hy' h
  rcases H with h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 64 h))))

/-- Standard subgroup formulation, with no nilpotence assumption on G. -/
theorem finite_odd_commutator_class2_of_covers {Bad : Triple→Prop}
    (check : FieldCover.{u,u} Bad) (pairs : PairCover.{u} Bad)
    (jets : JetCover.{u} Bad) (metab : MetaCover.{u}) (mix : RibbonOrder3.MixedOrder3Cover.{u})
    (h : LS (commutator G) 2=⊥) (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Good x y := by
  rw [←Subgroup.top_lowerCentralSeries_one] at h
  exact finite_odd_derived2_of_covers check pairs jets metab mix
    (RibbonDerivedTwo.of_derived_class2 h) x y odd hx hy

end RibbonOdd
#print axioms RibbonOdd.stationary_bound
#print axioms RibbonOdd.finite_odd_derived2_of_covers
#print axioms RibbonOdd.finite_odd_commutator_class2_of_covers
