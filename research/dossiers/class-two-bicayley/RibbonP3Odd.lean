import RibbonP3Local
import Ribbon5Family

namespace RibbonP3
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
open scoped commutatorElement
variable {G : Type*} [Group G]

abbrev Good (x y : G) := Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
  Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64

theorem flip_cycle {x y : G} {n : ℕ} (h : Ribbon.Cycle y x n) : Ribbon.Cycle x y n := by
  obtain ⟨w,inj,edges⟩ := h
  let flip : Bool × G → Bool × G := fun a => (!a.1,a.2)
  refine ⟨flip ∘ w, ?_, ?_⟩
  · intro i j e
    apply inj
    have e' := congrArg flip e
    simpa [flip,Function.comp_def] using e'
  · intro i
    have E := edges i
    change Ribbon.Adj x y (flip (w i))
      (flip (w ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))
    generalize w i = u at E ⊢
    generalize w ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ = v at E ⊢
    rcases u with ⟨a,u⟩
    rcases v with ⟨b,v⟩
    cases a <;> cases b <;> simpa [Ribbon.Adj,flip,Function.comp_def] using E

private theorem swap_c (x y : G) : portC y x=(portC x y)⁻¹ := by
  simp only [portC,commutatorElement_inv]

private theorem swap_u (nil : LS G 3=⊥) (x y : G) :
    portU y x=(portV x y)⁻¹ := by
  unfold portU
  rw [swap_c,commutatorElement_inv_left,←commutatorElement_inv]
  change (portC x y)⁻¹ * (portV x y)⁻¹ * portC x y=(portV x y)⁻¹
  have e := (center_of_L2 nil (layer_v x y) (portC x y)⁻¹).symm.inv_right.eq
  rw [e,mul_assoc,inv_mul_cancel,mul_one]

private theorem comm_class_two [Finite G] (odd : Odd (Nat.card G))
    (x y : G) (hx : x ≠1) (hy : y≠1) (nil : LS G 2=⊥) : Good x y := by
  have c (w : G) : Commute (portC x y) w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := next_layer (layer_c x y) w
    rwa [nil,Subgroup.mem_bot] at h
  have R := Ribbon.class2_pair x y (portC x y) (c x) (c y) (ports_xy x y) hx
    (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
  exact R.imp_right (fun z => z.imp_right Or.inl)

theorem generated_odd [Finite G] (nil : LS G 5=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) : Good x y := by
  let p := QuotientGroup.mk' (LS G 3)
  let F := QuotientGroup.mk' (LS G 2)
  have LSle : LS G 3 ≤ LS G 2 := Subgroup.lowerCentralSeries_antitone ⊤ (by decide : 2≤3)
  let f : (G ⧸ LS G 3) →* (G ⧸ LS G 2) :=
    QuotientGroup.lift _ F (by rwa [QuotientGroup.ker_mk'])
  have eval (g : G) : f (p g) = F g := rfl
  have nilH : LS (G ⧸ LS G 3) 3=⊥ := by
    rw [←map_ls p (QuotientGroup.mk'_surjective _) 3,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have gh := map_gen p (QuotientGroup.mk'_surjective _) gen
  have ker : f.ker = LS (G ⧸ LS G 3) 2 := by
    rw [←map_ls p (QuotientGroup.mk'_surjective _) 2]
    ext z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (LS G 3) z
    constructor
    · intro h
      have h' : F g=1 := h
      exact Subgroup.mem_map_of_mem p ((QuotientGroup.eq_one_iff _).mp h')
    · rintro ⟨v,hv,e⟩
      change f (p g)=1
      rw [← e,eval]
      exact (QuotientGroup.eq_one_iff _).mpr hv
  have cMap (a b : G) : p (portC a b)=portC (p a) (p b) := by
    simp only [portC,map_commutatorElement,map_inv]
  by_cases c0 : portC x y ∈ LS G 2
  · have h := Ribbon5GeneratorDrop.comm_if_projected_trivial nil x y gen c0
    have R := Ribbon.class2_pair x y (portC x y) (h ▸ Commute.one_left x) (h ▸ Commute.one_left y)
      (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact R.imp_right (fun z => z.imp_right Or.inl)
  · let C := F (portC x y)
    have C0 : C ≠ 1 := fun e => c0 ((QuotientGroup.eq_one_iff _).mp e)
    have oddQ := HaarClass3Separation64.odd_projection odd
    by_cases o3 : orderOf C = 3
    · by_cases u0 : portU (p x) (p y) = 1
      · by_cases v0 : portV (p x) (p y) = 1
        · have bot : LS (G ⧸ LS G 3) 2=⊥ := by
            rw [L2_eq_two nilH _ _ gh,u0,v0]
            apply bot_unique
            apply (Subgroup.closure_le _).mpr
            intro z hz
            simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl <;> exact Subgroup.one_mem _
          have le : LS G 2 ≤ LS G 3 := by
            rwa [←map_ls p (QuotientGroup.mk'_surjective _) 2,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at bot
          have e : LS G 2 = LS G 3 := le_antisymm le LSle
          have e' : LS G 3 = LS G 4 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e
          have e'' : LS G 4 = LS G 5 := congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) e'
          exact comm_class_two odd x y hx hy (e.trans (e'.trans (e''.trans nil)))
        · have altNZ : portU (p y) (p x)≠1 := by
            intro h
            rw [swap_u nilH] at h
            exact v0 (inv_eq_one.mp h)
          have altGen : Generates (p y) (p x) := by unfold Generates at gh ⊢; rwa [Set.pair_comm]
          have altO : orderOf (f (portC (p y) (p x)))=3 := by
            rw [swap_c,map_inv,orderOf_inv,←cMap,eval]
            exact o3
          exact Or.inr (Or.inr (Or.inr ((local_p3 nil y x p f nilH altGen ker altO altNZ).imp flip_cycle flip_cycle)))
      · have O : orderOf (f (portC (p x) (p y)))=3 := by rw [←cMap,eval]; exact o3
        exact Or.inr (Or.inr (Or.inr (local_p3 nil x y p f nilH gh ker O u0)))
    · have good (k : Nat) (a : 1 ≤ k) (b : k≤4) : C^k≠1 := by
        interval_cases k
        · simpa only [pow_one] using C0
        · simpa only [pow_two] using HaarClass3Odd.odd_no_involution oddQ C0
        · intro h
          have D := orderOf_dvd_iff_pow_eq_one.mpr h
          rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp D with z|z
          · exact C0 (orderOf_eq_one_iff.mp z)
          · exact o3 z
        · intro eq
          have h2 := HaarClass3Odd.odd_no_involution oddQ C0
          have no2 := HaarClass3Odd.odd_no_involution oddQ h2
          rw [←pow_mul] at no2
          exact no2 eq
      exact Or.inr (Or.inr (Or.inr (Ribbon5Bridge.local_bound nil x y good)))

theorem odd_class5 [Finite G] (nil : LS G 5=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) : Good x y := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_odd (pair_nil x y 5 nil) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) hx' hy' with h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 64 h))))

end RibbonP3
#print axioms RibbonP3.generated_odd
#print axioms RibbonP3.odd_class5
