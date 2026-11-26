import RibbonP11Exceptional

namespace RibbonP11
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine RibbonClass4Fallback
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

theorem derived_nil (d2 : RibbonDerivedTwo.D2 G) : LS (D G) 2=⊥ := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr
  change ⁅(⊤ : Subgroup (D G)),⊤⁆ ≤ Subgroup.center (D G)
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  apply Subgroup.mem_center_iff.mpr
  intro z
  exact Subtype.ext (d2 a.val a.property b.val b.property z.val z.property).symm.eq

/-- The complete stationary reduction. The three typed finite-geometry
callbacks are its only graph-specific premises. -/
theorem stationary_bound {Bad : F×F→Prop} (check : FieldCover.{u,u} Bad)
    (checkSmall : FieldCover.{u,0} Bad) (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) (hc : portC x y∈LS G 2) :
    Good x y := by
  by_contra no
  have stat := RibbonAffine.stationary x y gen hc
  let A := Abelianization (D G)
  letI : Finite A := Finite.of_surjective (Abelianization.of : D G→*A) (QuotientGroup.mk'_surjective (commutator (D G)))
  have primes (p : ℕ) (prime : Nat.Prime p) (div : p ∣ Nat.card A) : p=11 := by
    letI : Fact p.Prime := ⟨prime⟩
    exact no_other_prime check d2 x y gen odd no3 stat no p prime (prime_mod_nontrivial p div)
  letI : IsCyclic (PGroup G 11) := mod11_cyclic check checkSmall pairs jets d2 x y gen odd no3 stat no
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : IsCyclic A := cyclic_of_single_prime 11 primes
  have cyc : IsCyclic (D G) := cyclic_of_abelianization ⟨2,derived_nil d2⟩
  letI : IsCyclic (D G) := cyc
  letI : CommGroup (D G) := IsCyclic.commGroup
  have m : RibbonMeta.Meta G := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : D G) (⟨b,hb⟩ : D G))
  exact no (metab m x y odd hx hy)

/-- Interface for the other branch, with nontrivial image in the
class-two quotient of the pair-generated subgroup. -/
def NonStationaryCover : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (d2 : RibbonDerivedTwo.D2 G) (x y : G),
    Generates x y → Odd (Nat.card G) → (¬3 ∣ Nat.card G) → x≠1 → y≠1 → portC x y ∉ LS G 2 → Good x y

theorem finite_odd_derived2_of_covers {Bad : F×F→Prop} (check : FieldCover.{u,u} Bad)
    (checkSmall : FieldCover.{u,0} Bad) (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (nonstat : NonStationaryCover.{u})
    (d2 : RibbonDerivedTwo.D2 G) (x y : G) (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Good x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  have d := RibbonDerivedTwo.subgroup_d2 d2 S
  have gen := pair_generates x y
  have od := Odd.of_dvd_nat odd dvd
  have n3 : ¬3 ∣ Nat.card S := fun e => no3 (dvd_trans e dvd)
  have H : Good (leftPort x y) (rightPort x y) := by
    by_cases h : portC (leftPort x y) (rightPort x y) ∈ LS S 2
    · exact stationary_bound check checkSmall pairs jets metab d _ _ gen od n3 hx' hy' h
    · exact nonstat d _ _ gen od n3 hx' hy' h
  rcases H with h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 64 h))))

end RibbonP11
#print axioms RibbonP11.stationary_bound
#print axioms RibbonP11.finite_odd_derived2_of_covers
