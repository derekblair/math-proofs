import RibbonDerived3Small
namespace RibbonDerived3
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem comm_if_projected_trivial (n : Nat) (nil : LS G n=⊥) (lo : 2≤n) (x y : G)
    (gen : Generates x y) (hc : portC x y∈LS G 2) : portC x y=1 := by
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
  have d : LS G 1=LS G 2 :=
    le_antisymm h ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 1≤2))
  have stable (j : Nat) : LS G (1+j)=LS G 1 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change ⁅LS G (1+j),(⊤ : Subgroup G)⁆=LS G 1
      rw [ih]
      exact d.symm
  have all := stable (n-1)
  rw [show 1+(n-1)=n by omega,nil,eq_comm] at all
  have hC := layer_c x y
  rw [all,Subgroup.mem_bot] at hC
  exact hC

private theorem generated_odd_not_three [Finite G] (dnil : DLS G 3=⊥) (n : Nat) (nil : LS G n=⊥) (lo : 2≤n) (x y : G)
    (gen : Generates x y) (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G)
    (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  have hy2 := HaarClass3Odd.odd_no_involution odd hy
  let C := (QuotientGroup.mk' (LS G 2) (portC x y))
  by_cases c1 : C=1
  · have c := comm_if_projected_trivial n nil lo x y gen ((QuotientGroup.eq_one_iff _).mp c1)
    have z : Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 :=
      Ribbon.class2_pair x y (portC x y) (c ▸ Commute.one_left x) (c ▸ Commute.one_left y)
        (ports_xy x y) hx (by simpa only [pow_two] using hy2)
    exact z.imp_right (fun z => z.imp_right Or.inl)
  · by_cases o5 : orderOf C=5
    · exact projected_order_5_or_7 dnil n nil lo 0 x y gen hx
        (by simpa only [pow_two] using hy2) o5
    by_cases o7 : orderOf C=7
    · exact projected_order_5_or_7 dnil n nil lo 1 x y gen hx
        (by simpa only [pow_two] using hy2) o7
    have good (k : Nat) (lo : 1≤k) (hi : k≤7) : C^k≠1 := by
      intro E
      have d := orderOf_dvd_iff_pow_eq_one.mpr E
      have le := (Nat.le_of_dvd (by omega : 0<k) d).trans hi
      have D : orderOf C ∣ Nat.card G := dvd_trans (orderOf_dvd_natCard C) (LS G 2).card_quotient_dvd_card
      have O := Odd.of_dvd_nat odd D
      have small : orderOf C=1 ∨ orderOf C=3 ∨ orderOf C=5 ∨ orderOf C=7 := by
        obtain ⟨v,h⟩ := O
        omega
      rcases small with H|H|H|H
      · exact c1 (orderOf_eq_one_iff.mp H)
      · exact no3 (H ▸ D)
      · exact o5 H
      · exact o7 H
    exact Or.inr (Or.inr (Or.inr (local_bound dnil x y good)))

theorem inherited (S : Subgroup G) (dnil : DLS G 3=⊥) : DLS S 3=⊥ := by
  let f := S.subtype
  have incl : (Derived S).map f ≤ Derived G := Subgroup.lowerCentralSeries_map_subtype_le S 1
  have h := (Subgroup.lowerCentralSeries_mono 3) incl
  change ((Derived S).map f).lowerCentralSeries 3 ≤ DLS G 3 at h
  rw [←Subgroup.map_lowerCentralSeries,dnil] at h
  apply le_bot_iff.mp
  intro z hz
  have j := h (Subgroup.mem_map_of_mem f hz)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact Subgroup.mem_bot.mp j

/-- Finite odd-order nilpotent single-matching bi-Cayley graph with derived group
of class at most three and order not divisible by 3. Ambient nilpotency class is unrestricted. -/
theorem odd_not_three [Finite G] (dnil : DLS G 3=⊥) (nil : ∃ n, LS G n=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  obtain ⟨n,hn⟩ := nil
  let m := max 2 n
  have nm : LS G m=⊥ := le_bot_iff.mp (by
    rw [←hn]
    exact Subgroup.lowerCentralSeries_antitone _ (Nat.le_max_right _ _))
  rcases generated_odd_not_three (inherited S dnil) m (pair_nil x y m nm) (Nat.le_max_left _ _) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) (fun t => no3 (dvd_trans t dvd)) hx' hy' with h|h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 64 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 128 h)))))

end RibbonDerived3
#print axioms RibbonDerived3.odd_not_three
