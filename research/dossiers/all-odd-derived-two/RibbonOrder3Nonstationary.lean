import RibbonDerivedTwoP3
import RibbonOrder3Stable
import RibbonDerivedTwoLow
import RibbonP3Odd

namespace RibbonOrder3
open RibbonP3 RibbonDerivedTwo HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
open scoped commutatorElement
universe u
variable {G : Type u} [Group G]

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
    (x y : G) (hx : x ≠1) (hy : y≠1) (nil : LS G 2=⊥) : RibbonP3.Good x y := by
  have c (w : G) : Commute (portC x y) w := by
    apply commutatorElement_eq_one_iff_commute.mp
    have h := next_layer (layer_c x y) w
    rwa [nil,Subgroup.mem_bot] at h
  have R := Ribbon.class2_pair x y (portC x y) (c x) (c y) (ports_xy x y) hx
    (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
  exact R.imp_right (fun z => z.imp_right Or.inl)

/-- Interface used by the joint affine / projected-order-three templates. -/
def MixedOrder3Cover : Prop :=
  ∀ {G K : Type u} [Group G] [Field K] [Finite G] [Finite K]
    (d2 : D2 G) (x y : G) (μ : G→*Kˣ) (τ : G→K),
    Odd (Nat.card G) → (2:K)≠0 →
    orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3 →
    RibbonP11.IsCocycle μ τ → RibbonP11.Normalized (RingHom.id K) x y μ τ →
    (μ x)^(Nat.card G)=1 → (μ y)^(Nat.card G)=1 → RibbonP3.Good x y

/-- All nonstationary cases in odd finite groups with class-two derived
subgroup, given only the external mixed order-three template checker. -/
theorem nonstationary_bound [Finite G] (cert : MixedOrder3Cover.{u}) (m : D2 G)
    (x y : G) (gen : Generates x y) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) (c0 : portC x y ∉ LS G 2) : RibbonP3.Good x y := by
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
  let C := F (portC x y)
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
        by_cases nn : LS G 2=⊥
        · exact comm_class_two odd x y hx hy nn
        · obtain ⟨K,F,fin,μ,τ,two,co,normal,px,py⟩ := stable_third_affine m x y gen odd e nn
          exact cert m x y μ τ odd two o3 co normal px py
      · have altNZ : portU (p y) (p x)≠1 := by
          intro h
          rw [swap_u nilH] at h
          exact v0 (inv_eq_one.mp h)
        have altGen : Generates (p y) (p x) := by unfold Generates at gh ⊢; rwa [Set.pair_comm]
        have altO : orderOf (f (portC (p y) (p x)))=3 := by
          rw [swap_c,map_inv,orderOf_inv,←cMap,eval]
          exact o3
        exact Or.inr (Or.inr (Or.inr ((local_p3 m y x p f nilH altGen ker altO altNZ).imp flip_cycle flip_cycle)))
    · have O : orderOf (f (portC (p x) (p y)))=3 := by rw [←cMap,eval]; exact o3
      exact Or.inr (Or.inr (Or.inr (local_p3 m x y p f nilH gh ker O u0)))
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
    exact Or.inr (Or.inr (Or.inr (RibbonDerivedTwo.local_bound m x y good)))

end RibbonOrder3
#print axioms RibbonOrder3.nonstationary_bound
