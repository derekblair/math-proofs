import HaarP3LayerGenModels

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate
variable {G : Type*} [Group G]

theorem ls4quot_class4 (G : Type*) [Group G] : LS (G ⧸ LS G 4) 4=⊥ := by
  let f := QuotientGroup.mk' (LS G 4)
  rw [← map_ls f (QuotientGroup.mk'_surjective (LS G 4)), Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']

theorem ls4quot_exact4 (h : LS G 4≠⊥) (nil : LS G 5=⊥) :
    LS (G ⧸ LS G 4) 3≠⊥ := by
  intro e
  let f := QuotientGroup.mk' (LS G 4)
  have M := map_ls f (QuotientGroup.mk'_surjective (LS G 4)) 3
  rw [e, Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at M
  have rel := le_antisymm M
    (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 3≤4))
  have eq : LS G 4=LS G 5 :=
    congrArg (fun S : Subgroup G => ⁅S,(⊤ : Subgroup G)⁆) rel
  exact h (eq.trans nil)

theorem ls2_map_card_in_ls4quot :
    let f := QuotientGroup.mk' (LS G 4)
    let Q := G ⧸ LS G 4
    Nat.card ((LS Q 2).map (QuotientGroup.mk' (LS Q 3))) =
      Nat.card ((LS G 2).map (QuotientGroup.mk' (LS G 3))) := by
  let N := LS G 4
  let M := LS G 3
  let f := QuotientGroup.mk' N
  let Q := G ⧸ N
  have hi : N ≤ M :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G) (by decide : 3≤4)
  have e : M.map f = LS Q 3 := map_ls f (QuotientGroup.mk'_surjective N) 3
  change Nat.card ((LS Q 2).map (QuotientGroup.mk' (LS Q 3))) = _
  have hc (A B : Subgroup Q) [A.Normal] [B.Normal] (h : A=B) :
      Nat.card ((LS Q 2).map (QuotientGroup.mk' A)) =
        Nat.card ((LS Q 2).map (QuotientGroup.mk' B)) := by
    subst B
    rfl
  refine (hc _ _ e.symm).trans ?_
  let F := QuotientGroup.quotientQuotientEquivQuotient N M hi
  let p := QuotientGroup.mk' (M.map f)
  have hcomp : (F.toMonoidHom.comp p).comp f = QuotientGroup.mk' M := by
    ext x
    exact QuotientGroup.quotientQuotientEquivQuotient_apply_mk N M hi x
  have heq : ((LS Q 2).map p).map F.toMonoidHom =
      (LS G 2).map (QuotientGroup.mk' M) := by
    rw [← map_ls f (QuotientGroup.mk'_surjective N), Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [←heq]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ F.toMonoidHom F.injective).toEquiv)

theorem models_ls4quot (h : LS G 4≠⊥) (nil : LS G 5=⊥)
    (x y : G) (gen : Generates x y)
    (size : Nat.card ((LS G 2).map (QuotientGroup.mk' (LS G 3)))=3) :
    let f := QuotientGroup.mk' (LS G 4)
    let E := make (ls4quot_class4 G) (f x) (f y)
    Nat.card (LS (G ⧸ LS G 4) 3)=3 ∧
    ((∃ j t e : Fin 3, orderOf E.a=3 ∧ E.v=E.u^j.val*E.a^t.val ∧
      E.u^3=E.a^e.val ∧ E.b=E.a^j.val ∧ E.d=E.a^(j.val*j.val)) ∨
    (∃ t e : Fin 3, orderOf E.d=3 ∧ E.u=E.d^t.val ∧
      E.v^3=E.d^e.val ∧ E.a=1 ∧ E.b=1)) := by
  let f := QuotientGroup.mk' (LS G 4)
  apply models (ls4quot_class4 G) (ls4quot_exact4 h nil) (f x) (f y)
    (map_gen f (QuotientGroup.mk'_surjective (LS G 4)) gen)
  exact ls2_map_card_in_ls4quot.trans size

end HaarP3LayerGen

#print axioms HaarP3LayerGen.models_ls4quot
