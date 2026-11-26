import RibbonD3ActivePrime
import RibbonDerived3Family

namespace RibbonD3Stationary
open RibbonP11 HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonAffine RibbonClass4Fallback RibbonDerived3
open RibbonOdd (Label)
universe u
variable {G : Type u} [Group G] [Finite G]

theorem derived_internal (n : Nat) (h : DLS G n=⊥) : LS (D G) n=⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h' := Subgroup.mem_map_of_mem (D G).subtype hx
  rw [Subgroup.top_subtype_lowerCentralSeries] at h'
  change x.val∈DLS G n at h'
  rw [h,Subgroup.mem_bot] at h'
  exact Subgroup.mem_bot.mpr (Subtype.ext h')

theorem widen {x y : G} (h : RibbonP3.Good x y) : LongGood x y := by
  rcases h with h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem stationary_bound {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (dnil : DLS G 3=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3∣Nat.card G)
    (hx : x≠1) (hy : y≠1) (hc : portC x y∈LS G 2) : LongGood x y := by
  by_contra no
  have stat := RibbonAffine.stationary x y gen hc
  let A := Abelianization (D G)
  letI : Finite A := Finite.of_surjective (Abelianization.of : D G→*A)
    (QuotientGroup.mk'_surjective (commutator (D G)))
  have pNotThree (p : Nat) (hp : p∣Nat.card A) : p≠3 := by
    intro e
    have cA : Nat.card A∣Nat.card (D G) :=
      (commutator (D G)).card_quotient_dvd_card
    exact no3 (e ▸ dvd_trans hp (dvd_trans cA (D G).card_subgroup_dvd_card))
  have cyclicA : IsCyclic A := by
    by_cases one : Nat.card A=1
    · letI : Subsingleton A := (Nat.card_eq_one_iff_unique.mp one).1
      infer_instance
    · obtain ⟨p,hp,pA⟩ := Nat.exists_prime_and_dvd one
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨cyc,hP,μ,τ,co,norm,bad⟩ := active_prime check pairs jets dnil x y gen odd no3 stat no p
        (pNotThree p pA) (prime_mod_nontrivial p pA)
      have only (q : ℕ) (hq : q.Prime) (qA : q∣Nat.card A) : q=p := by
        by_contra distinct
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨_,hQ,ν,σ,co',norm',bad'⟩ := active_prime check pairs jets dnil x y gen odd no3 stat no q
          (pNotThree q qA) (prime_mod_nontrivial q qA)
        have hlabel : Label p μ x y ≠ Label q ν x y := by
          intro e
          exact distinct (congrArg Prod.fst e).symm
        exact no (pairs dnil x y p q hP hQ μ ν τ σ odd no3 co co' norm norm' bad bad' hlabel)
      letI : IsCyclic (PGroup G p) := cyc
      exact cyclic_of_single_prime p only
  letI : IsCyclic A := cyclicA
  have cyc : IsCyclic (D G) := cyclic_of_abelianization ⟨3,derived_internal 3 dnil⟩
  letI : IsCyclic (D G) := cyc
  letI : CommGroup (D G) := IsCyclic.commGroup
  have m : RibbonMeta.Meta G := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a,ha⟩ : D G) (⟨b,hb⟩ : D G))
  exact no (widen (metab m x y odd hx hy))

def NonStationaryCover : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (dnil : DLS G 3=⊥) (x y : G),
    Generates x y → Odd (Nat.card G) → (¬3∣Nat.card G) → x≠1 → y≠1 →
    portC x y∉LS G 2 → LongGood x y

/-- Ambient-non-nilpotent class-three-derived bound, conditional on the
concrete chart certificates. -/
theorem from_covers {Bad : Triple→Prop} (check : FieldCover.{u,u} Bad)
    (pairs : PairCover.{u} Bad) (jets : JetCover.{u} Bad) (metab : MetaCover.{u})
    (nonstat : NonStationaryCover.{u})
    (dnil : DLS G 3=⊥) (x y : G) (odd : Odd (Nat.card G)) (no3 : ¬3∣Nat.card G)
    (hx : x≠1) (hy : y≠1) : LongGood x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  have d := RibbonDerived3.inherited S dnil
  have gen := pair_generates x y
  have od := Odd.of_dvd_nat odd dvd
  have n3 : ¬3 ∣ Nat.card S := fun e => no3 (dvd_trans e dvd)
  have H : LongGood (leftPort x y) (rightPort x y) := by
    by_cases h : portC (leftPort x y) (rightPort x y) ∈ LS S 2
    · exact stationary_bound check pairs jets metab d _ _ gen od n3 hx' hy' h
    · exact nonstat d _ _ gen od n3 hx' hy' h
  rcases H with h|h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h)))))

end RibbonD3Stationary
#print axioms RibbonD3Stationary.stationary_bound
#print axioms RibbonD3Stationary.from_covers
