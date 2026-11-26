import RibbonMetaDirect3
import RibbonMetaDrop
import RibbonClass4Fallback

namespace RibbonMeta
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
variable {G : Type*} [Group G]

/-- No finiteness, generation or nilpotence assumptions. In particular,
this applies when the projected commutator has odd finite order >1. -/
theorem local_C32 (m : Meta G) (x y : G)
    (h : (QuotientGroup.mk' (LS G 2) (portC x y))^4 ≠ 1) : Ribbon.Cycle x y 32 := by
  let C := QuotientGroup.mk' (LS G 2) (portC x y)
  have h2 : C^2≠1 := by
    intro eq
    apply h
    change C^(2*2)=1
    rw [pow_mul,eq,one_pow]
  have h1 : C≠1 := fun eq => h2 (by rw [eq,one_pow])
  by_cases o3 : orderOf C=3
  · exact direct3_cycle m x y o3
  · have good (k : Nat) (a : 1 ≤ k) (b : k ≤ 4) : C^k≠1 := by
      interval_cases k
      · simpa only [pow_one] using h1
      · exact h2
      · intro eq
        have D := orderOf_dvd_iff_pow_eq_one.mpr eq
        rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp D with z|z
        · exact h1 (orderOf_eq_one_iff.mp z)
        · exact o3 z
      · exact h
    exact low_cycle m x y good

theorem finite_odd_local_C32 [Finite G] (m : Meta G) (x y : G)
    (odd : Odd (Nat.card G))
    (h : QuotientGroup.mk' (LS G 2) (portC x y) ≠ 1) : Ribbon.Cycle x y 32 := by
  apply local_C32 m x y
  have O := HaarClass3Separation64.odd_projection odd
  have h2 := HaarClass3Odd.odd_no_involution O h
  have h4 := HaarClass3Odd.odd_no_involution O h2
  rw [←pow_mul] at h4
  exact h4

private theorem generated_odd_direct [Finite G] {n : ℕ} (nil : LS G n=⊥) (m : Meta G)
    (x y : G) (gen : Generates x y) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  by_cases c0 : portC x y ∈ LS G 2
  · have h := comm_if_projected_trivial nil x y gen c0
    have R := Ribbon.class2_pair x y (portC x y) (h ▸ Commute.one_left x) (h ▸ Commute.one_left y)
      (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact R.imp_right (fun z => z.imp_right Or.inl)
  · exact Or.inr (Or.inr (Or.inr (finite_odd_local_C32 m x y odd
      (fun e => c0 ((QuotientGroup.eq_one_iff _).mp e)))))

/-- The odd, nilpotent, metabelian single-matching ribbon theorem, with
no bound on the nilpotency class or requirement that the ports generate G. -/
theorem finite_odd_nilpotent [Finite G] (nil : ∃ n, LS G n=⊥) (m : Meta G)
    (x y : G) (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨ Ribbon.Cycle x y 32 := by
  obtain ⟨n,hn⟩ := nil
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_odd_direct (pair_nil x y n hn) (subgroup_meta m S) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) hx' hy' with h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (pair_lift x y 32 h)))

end RibbonMeta
#print axioms RibbonMeta.local_C32
#print axioms RibbonMeta.finite_odd_local_C32
#print axioms RibbonMeta.finite_odd_nilpotent
