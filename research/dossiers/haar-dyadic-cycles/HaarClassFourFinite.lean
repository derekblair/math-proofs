import HaarClass4Generate
import HaarClassThreeFinite

namespace HaarClassFourFinite
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate HaarClass4Projection HaarAllNoncommuting

variable {G H : Type*} [Group G] [Group H]

theorem swap_c (x y : G) : portC y x=(portC x y)⁻¹ := by
  simp only [portC,commutatorElement_def,inv_inv]
  group

theorem v_swaps_u (x y : G) (h : portV x y ∉ LS G 3) : portU y x ∉ LS G 3 := by
  intro e
  let f := QuotientGroup.mk' (LS G 3)
  have z : f (portU y x)=1 := (QuotientGroup.eq_one_iff _).mpr e
  rw [portU,map_commutatorElement,swap_c x y,map_inv] at z
  have commute : Commute (f (portC x y))⁻¹ (f y) := commutatorElement_eq_one_iff_commute.mp z
  have q := commutatorElement_eq_one_iff_commute.mpr commute.inv_left
  have q2 : f (portV x y)=1 := by
    rw [portV,map_commutatorElement]
    simpa only [inv_inv] using q
  exact h ((QuotientGroup.eq_one_iff _).mp q2)

theorem mapped_cycle (f : G →* H) (hf : Function.Injective f) (x y : G) {n : ℕ}
    (h : HasCycle x y n) : HasCycle (f x) (f y) n := by
  obtain ⟨B,inj,adj⟩ := h
  let W : Fin n → Bool × H := fun i => ((B i).1, f (B i).2)
  refine ⟨W,?_ ,?_⟩
  · intro a b h
    apply inj
    exact Prod.ext (congrArg (fun z : Bool × H => z.1) h)
      (hf (congrArg (fun z : Bool × H => z.2) h))
  · intro i
    let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    have d := adj i
    change HaarCycle.haarAdj x y (B i) (B j) at d
    change HaarCycle.haarAdj (f x) (f y) (W i) (W j)
    cases he : (B i).1 <;> simp [HaarCycle.haarAdj,he] at d
    all_goals
      obtain ⟨s,d⟩ := d
      rcases d with e|e|e <;> simp [HaarCycle.haarAdj,W,he,s,e]

theorem from_u (h : LS G 4=⊥) (x y : G) {p : ℕ} [Fact p.Prime]
    (HP : IsPGroup p G) (np : p≠2) (hu : portU x y ∉ LS G 3) :
    HasCycle x y 32 := by
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
  exact HaarClass4Prime.prime_certificate M φ ψ hφ hψ
    (HP.of_surjective φ (QuotientGroup.mk'_surjective _)) np nc nz

theorem generating_pair_class_four (h : LS G 4=⊥) (deep : LS G 3≠⊥) (x y : G)
    (gen : Generates x y) {p : ℕ} [Fact p.Prime] (HP : IsPGroup p G) (np : p≠2) :
    HasCycle x y 32 := by
  rcases deep_survives x y gen h deep with su | sv
  · exact from_u h x y HP np su
  · obtain ⟨W,inj,adj⟩ := from_u h y x HP np (v_swaps_u x y sv)
    exact ⟨W,inj,fun i => HaarClass3Odd.adj_flip.mpr (adj i)⟩

theorem generated_group [Finite G] (h : LS G 4=⊥) (x y : G)
    (gen : Generates x y) {p : ℕ} [Fact p.Prime] (HP : IsPGroup p G) (np : p≠2)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  by_cases e : LS G 3=⊥
  · have odd : Odd (Nat.card G) := by
      obtain ⟨n, r⟩ := HP.exists_card_eq
      rw [r]
      exact ((Nat.Prime.odd_of_ne_two Fact.out np)).pow
    exact HaarClass3Odd.class_three odd (by simpa only [HaarClassThreeFinite.fourth_is_fourth] using e) x y hx hy hxy
  exact Or.inr (Or.inr (Or.inr (generating_pair_class_four h e x y gen HP np)))

theorem lift_pair [Finite G] (h : LS G 4=⊥) (x y : G) {p : ℕ} [Fact p.Prime]
    (HP : IsPGroup p G) (np : p≠2) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
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
  have C := generated_group cls X Y gen (HP.to_subgroup S) np x₁ y₁ xy
  have map (n : ℕ) : HasCycle X Y n → HasCycle x y n :=
    mapped_cycle S.subtype Subtype.val_injective X Y
  rcases C with C|C|C|C
  · exact Or.inl (map 4 C)
  · exact Or.inr (Or.inl (map 8 C))
  · exact Or.inr (Or.inr (Or.inl (map 16 C)))
  · exact Or.inr (Or.inr (Or.inr (map 32 C)))

end HaarClassFourFinite

#print axioms HaarClassFourFinite.lift_pair

#print axioms HaarClassFourFinite.generating_pair_class_four
