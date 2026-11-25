import FiberBounds
namespace CoverCutoff

abbrev SmallPack (h : ℕ) := {p : Equiv.Perm (Fin (SmallN (h+1))) // Packs patternA 2 (h+1) p}
abbrev BigPack (h : ℕ) (hh : 2≤h) :=
  {p : Equiv.Perm (Fin (BigN h (h+1))) // Packs (delayed h hh) 3 (h+1) p}
abbrev GapPack (h : ℕ) := {p : SmallPack h // FiberGap p.val}

noncomputable def branchLift (h : ℕ) (hh : 2≤h) : SmallPack h ⊕ GapPack h → BigPack h hh
  | .inl p => ⟨liftRanks p.val true,lift_packs hh (by omega) p.val p.prop true⟩
  | .inr p => ⟨liftRanks p.val.val false,lift_packs hh (by omega) p.val.val p.val.prop false⟩

lemma branchLift_inj {h : ℕ} (hh : 2≤h) : Function.Injective (branchLift h hh) := by
  intro p q H
  have cmp (x y : SmallPack h) (a b : Bool)
      (e : liftRanks (h:=h) x.val a = liftRanks (h:=h) y.val b) : x=y := by
    apply Subtype.ext
    have he := congrArg (restrictSmall h (h+1) hh (by omega)) e
    exact (restrict_lift hh (by omega) x.val a).symm.trans
      (he.trans (restrict_lift hh (by omega) y.val b))
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (cmp p q true true (congrArg Subtype.val H))
    | inr q =>
      have Hb := fiber_true_before hh p.val p.prop
      have nHb := fiber_false_after hh q.val.val q.prop
      have E : liftRanks (h:=h) p.val true = liftRanks (h:=h) q.val.val false := congrArg Subtype.val H
      exact (nHb (E ▸ Hb)).elim
  | inr p =>
    cases q with
    | inl q =>
      have Hb := fiber_true_before hh q.val q.prop
      have nHb := fiber_false_after hh p.val.val p.prop
      have E : liftRanks (h:=h) q.val true = liftRanks (h:=h) p.val.val false := congrArg Subtype.val H.symm
      exact (nHb (E ▸ Hb)).elim
    | inr q =>
      exact congrArg Sum.inr (Subtype.ext (cmp p.val q.val false false (congrArg Subtype.val H)))

lemma branchLift_surj {h : ℕ} (hh : 2≤h) : Function.Surjective (branchLift h hh) := by
  classical
  intro q
  let j := h+1
  have hj : 1≤j := by omega
  let p : SmallPack h := ⟨restrictSmall h j hh hj q.val,restrict_packs hh hj q.val q.prop⟩
  by_cases hb : FiberBefore q.val
  · refine ⟨Sum.inl p,Subtype.ext ?_⟩
    exact restrict_inj_next hh hj rfl _ _ (lift_packs hh hj p.val p.prop true)
      q.prop (restrict_lift hh hj p.val true) (iff_of_true (fiber_true_before hh p.val p.prop) hb)
  · have hg : FiberGap p.val := by
      by_contra! ng
      exact hb (fiberBefore_of_no_gap hh q.val q.prop ng)
    refine ⟨Sum.inr ⟨p,hg⟩,Subtype.ext ?_⟩
    exact restrict_inj_next hh hj rfl _ _ (lift_packs hh hj p.val p.prop false)
      q.prop (restrict_lift hh hj p.val false) (iff_of_false (fiber_false_after hh p.val hg) hb)

theorem first_difference_eq_gap_count {h : ℕ} (hh : 2≤h) :
    packCount (delayed h hh) 3 (h+1) =
      packCount patternA 2 (h+1) + Nat.card (GapPack h) := by
  classical
  have hcard := Nat.card_congr (Equiv.ofBijective (branchLift h hh)
    ⟨branchLift_inj hh,branchLift_surj hh⟩)
  letI : Fintype (SmallPack h) := Fintype.ofFinite _
  letI : Fintype (GapPack h) := Fintype.ofFinite _
  change Nat.card (BigPack h hh) = Nat.card (SmallPack h) + Nat.card (GapPack h)
  rw [←hcard,Nat.card_eq_fintype_card,Fintype.card_sum,←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card]

#print axioms first_difference_eq_gap_count
end CoverCutoff
