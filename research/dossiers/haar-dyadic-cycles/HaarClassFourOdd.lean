import HaarClassFourFinite

namespace HaarClassFourOdd

open HaarClass4Normal HaarClass4Table HaarClass4Projection HaarClass4Certificates
open HaarClass4Gate HaarClass4Structure HaarClass4Ports HaarClass4Generate HaarClassFourFinite HaarAllNoncommuting

variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem odd_detect (odd : Odd (Nat.card H)) {g : H} (hg : g≠1)
    {n : ℤ} (s : small n) : g^n≠1 := by
  intro e
  have d := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (orderOf_dvd_iff_zpow_eq_one.mpr e))
  have ab : |n| = (n.natAbs:ℤ) := (Int.natCast_natAbs n).symm
  have d4 : n.natAbs ∣ (4:ℕ) := by
    rcases s with s|s|s
    · have q : n.natAbs=1 := by omega
      rw [q]; decide
    · have q : n.natAbs=2 := by omega
      rw [q]; decide
    · have q : n.natAbs=4 := by omega
      rw [q]
  have dv := d.trans d4
  rw [show (4:ℕ)=2^2 by decide] at dv
  obtain ⟨i,_,di⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dv
  by_cases iz : i=0
  · exact hg (orderOf_eq_one_iff.mp (by simpa only [iz,pow_zero] using di))
  · have so := Odd.of_dvd_nat odd (orderOf_dvd_natCard g)
    exact so.not_two_dvd_nat (by rw [di]; exact dvd_pow_self 2 iz)

theorem odd_certificate (M : Data G) (φ : G →* H) (ψ : G →* K)
    (hφ : KillsMid M φ) (hψ : KillsTail M ψ) (odd : Odd (Nat.card H))
    (hc : φ M.c≠1) (deep : ψ M.u≠1) : HasCycle M.x M.y 32 := by
  by_cases F : M.c^3=M.u*M.v
  · have q : (φ M.c)^(3:ℕ)=1 := by simpa [hφ.u,hφ.v] using congrArg φ F
    have r := orderOf_dvd_iff_pow_eq_one.mpr q
    have order : orderOf (φ M.c)=3 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp r with t|t
      · exact (hc (orderOf_eq_one_iff.mp t)).elim
      · exact t
    have ord3 (n : ℤ) (h : n%3≠0) : (φ M.c)^n≠1 := by
      intro eq
      have v := orderOf_dvd_iff_zpow_eq_one.mpr eq
      rw [order] at v
      exact h (Int.emod_eq_zero_of_dvd v)
    have h := (first_cubes M F).1
    have c : HaarClass4CollectCore.Central (M.u^3) := h.symm ▸ HaarClass4Powers.central_mul M.ca M.cb
    exact conditional_simple M φ hφ ord3 F h (cube_center M.x M.u M.a M.ca M.ux c)
  · exact ordinary_simple M φ ψ hφ hψ (fun _ s => odd_detect odd hc s) deep
      (fun h => F ((first_is_one M).mp h)) (fun h => F (second_implies_first M h))

theorem from_u_odd (h : LS G 4=⊥) (x y : G) (odd : Odd (Nat.card G))
    (hu : portU x y ∉ LS G 3) : HasCycle x y 32 := by
  let φ := QuotientGroup.mk' (LS G 2)
  let ψ := QuotientGroup.mk' (LS G 3)
  let M := make h x y
  have ⟨a,b,d⟩ := tail_layers h x y
  have mid : LS G 3 ≤ LS G 2 := (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 2 ≤ 3)
  have hφ : KillsMid M φ :=
    ⟨⟨(QuotientGroup.eq_one_iff _).mpr (mid a),(QuotientGroup.eq_one_iff _).mpr (mid b),
      (QuotientGroup.eq_one_iff _).mpr (mid d)⟩,
      (QuotientGroup.eq_one_iff _).mpr (layer_u x y),(QuotientGroup.eq_one_iff _).mpr (layer_v x y)⟩
  have hψ : KillsTail M ψ :=
    ⟨(QuotientGroup.eq_one_iff _).mpr a,(QuotientGroup.eq_one_iff _).mpr b,(QuotientGroup.eq_one_iff _).mpr d⟩
  have nz : ψ M.u≠1 := fun e => hu ((QuotientGroup.eq_one_iff _).mp e)
  have nc : φ M.c≠1 := by
    intro e
    have mc : portC x y ∈ LS G 2 := (QuotientGroup.eq_one_iff _).mp e
    exact hu (next_layer mc x)
  exact odd_certificate M φ ψ hφ hψ (Odd.of_dvd_nat odd (LS G 2).card_quotient_dvd_card) nc nz

theorem generating_odd_exact_four (h : LS G 4=⊥) (deep : LS G 3≠⊥) (x y : G)
    (gen : Generates x y) (odd : Odd (Nat.card G)) : HasCycle x y 32 := by
  rcases deep_survives x y gen h deep with su | sv
  · exact from_u_odd h x y odd su
  · obtain ⟨W,inj,adj⟩ := from_u_odd h y x odd (v_swaps_u x y sv)
    exact ⟨W,inj,fun i => HaarClass3Odd.adj_flip.mpr (adj i)⟩

theorem generated_odd (h : LS G 4=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  by_cases e : LS G 3=⊥
  · exact HaarClass3Odd.class_three odd
      (by simpa only [HaarClassThreeFinite.fourth_is_fourth] using e) x y hx hy hxy
  exact Or.inr (Or.inr (Or.inr (generating_odd_exact_four h e x y gen odd)))

theorem odd_class_four (h : LS G 4=⊥) (x y : G) (odd : Odd (Nat.card G))
    (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  have cls : LS S 4=⊥ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot,Subgroup.top_subtype_lowerCentralSeries,← le_bot_iff]
    exact (Subgroup.lowerCentralSeries_mono 4 (show S≤⊤ from le_top)).trans (le_of_eq h)
  have x₁ : X≠1 := fun e => hx (congrArg Subtype.val e)
  have y₁ : Y≠1 := fun e => hy (congrArg Subtype.val e)
  have xy : X≠Y := fun e => hxy (congrArg Subtype.val e)
  have C := generated_odd cls X Y gen (Odd.of_dvd_nat odd S.card_subgroup_dvd_card) x₁ y₁ xy
  have map (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    mapped_cycle S.subtype Subtype.val_injective X Y
  rcases C with C|C|C|C
  · exact Or.inl (map 4 C)
  · exact Or.inr (Or.inl (map 8 C))
  · exact Or.inr (Or.inr (Or.inl (map 16 C)))
  · exact Or.inr (Or.inr (Or.inr (map 32 C)))

end HaarClassFourOdd

#print axioms HaarClassFourOdd.odd_class_four
