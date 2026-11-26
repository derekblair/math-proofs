import RibbonOddPairPacked
import RibbonOrderThreeUse
import RibbonOddLabels

namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonP11Charts RibbonStationaryChart
open RibbonDerived3 RibbonOdd
universe u
variable {G : Type u} [Group G]
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem pair_sound {i j : Fin 28} (lt : i.val<j.val)
    (p q : Fin 64) (n : p.val<q.val)
    (e : affPt (inputs i).p (inputs i).a (inputs i).b (pickPair i j) p =
         affPt (inputs i).p (inputs i).a (inputs i).b (pickPair i j) q)
    (f : affPt (inputs j).p (inputs j).a (inputs j).b (pickPair i j) p =
         affPt (inputs j).p (inputs j).a (inputs j).b (pickPair i j) q) :
    IsMate (spec (pickPair i j)) p.val q.val := by
  have h := pairs_checked i j lt
  unfold checkPair at h
  have h' := List.all_eq_true.mp h p.val (List.mem_range.mpr p.isLt)
  have h'' := List.all_eq_true.mp h' q.val (List.mem_range.mpr q.isLt)
  simpa only [decide_eq_true n,aff_at,congrArg (affPack _) e,congrArg (affPack _) f,
    beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h''

theorem field_sound (i : Fin 28) (x y : G)
    (μ : G →* (ZMod (inputs i).p)ˣ) (τ : G→ZMod (inputs i).p)
    (co : Aff μ τ) (norm : RibbonP11.Normalized (RingHom.id _) x y μ τ)
    (lab : Label (inputs i).p μ x y=inputLabel i) (k : Count) (p q : Fin 64)
    (e : Ribbon5Bridge.pathAt x y (spec k).T.toArray p.val =
      Ribbon5Bridge.pathAt x y (spec k).T.toArray q.val) :
    affPt (inputs i).p (inputs i).a (inputs i).b k p =
    affPt (inputs i).p (inputs i).a (inputs i).b k q := by
  let z := inputs i
  letI : Fact z.p.Prime := ⟨inputs_prime i⟩
  have v := Prod.mk.inj ((Prod.mk.inj lab).2)
  have X : (μ x: ZMod z.p)=digit z.p z.a := by
    rw [←ZMod.natCast_zmod_val (μ x: ZMod z.p)]
    exact congrArg (digit z.p) v.1
  have Y : (μ y: ZMod z.p)=digit z.p z.b := by
    rw [←ZMod.natCast_zmod_val (μ y: ZMod z.p)]
    exact congrArg (digit z.p) v.2
  have h := invert_inputs i
  have a := RibbonP11Pair.inv_unit_of (μ x) ((digit z.p z.a)^(z.p-2)) (by rw [X]; exact h.1)
  have b := RibbonP11Pair.inv_unit_of (μ y) ((digit z.p z.b)^(z.p-2)) (by rw [Y]; exact h.2)
  have tx : τ x=coeffX z.p z.a := by
    rcases norm with ⟨nz,x0,_⟩|⟨zz,_,x1,_⟩
    · have N : z.a≠1 := fun h => nz (X.trans ((digit_one i).2 h))
      simp [x0,coeffX,N]
    · have Z : z.a=1 := (digit_one i).1 (X.symm.trans zz)
      simp [x1,coeffX,Z]
  have ty : τ y=coeffY z.p z.a := by
    rcases norm with ⟨nz,_,y1⟩|⟨zz,_,_,y0⟩
    · have N : z.a≠1 := fun h => nz (X.trans ((digit_one i).2 h))
      simp [y1,coeffY,N]
    · have Z : z.a=1 := (digit_one i).1 (X.symm.trans zz)
      simp [y0,coeffY,Z]
  simpa only [X,Y,a,b,tx,ty,affPt] using flatPosition_same μ τ co x y (spec k) p.val q.val e

theorem pairs_cover : PairCover.{u} Bad := by
  intro G _ _ d x y r s hr hs μ ν τ σ _ co co' n n' bad bad' ne
  obtain ⟨i,ei⟩ := bad
  obtain ⟨j,ej⟩ := bad'
  have ri : r=(inputs i).p := (Prod.mk.inj ei).1
  have sj : s=(inputs j).p := (Prod.mk.inj ej).1
  subst r
  subst s
  have hij : i≠j := fun h => ne (ei.trans (h ▸ ej.symm))
  have close (a b : Fin 28) (ab : a.val<b.val)
      (A : ∀ (k : Count) (p q : Fin 64),
        Ribbon5Bridge.pathAt x y (spec k).T.toArray p.val =
          Ribbon5Bridge.pathAt x y (spec k).T.toArray q.val →
          affPt (inputs a).p (inputs a).a (inputs a).b k p =
            affPt (inputs a).p (inputs a).a (inputs a).b k q)
      (B : ∀ (k : Count) (p q : Fin 64),
        Ribbon5Bridge.pathAt x y (spec k).T.toArray p.val =
          Ribbon5Bridge.pathAt x y (spec k).T.toArray q.val →
          affPt (inputs b).p (inputs b).a (inputs b).b k p =
            affPt (inputs b).p (inputs b).a (inputs b).b k q) :
      RibbonP11.Good x y := by
    apply Or.inr ∘ Or.inr ∘ Or.inr
    let k := pickPair a b
    let chart (p : Fin 64) := (affPt (inputs a).p (inputs a).a (inputs a).b k p,
      affPt (inputs b).p (inputs b).a (inputs b).b k p)
    exact from_state (RibbonP11Adapters.dnil d) k x y chart
      (fun p q e => Prod.ext (A k p q e) (B k p q e))
      (fun p q n e => pair_sound ab p q n (congrArg Prod.fst e) (congrArg Prod.snd e))
  rcases lt_or_gt_of_ne hij with h|h
  · exact close i j h (field_sound i x y μ τ co n ei) (field_sound j x y ν σ co' n' ej)
  · exact close j i h (field_sound j x y ν σ co' n' ej) (field_sound i x y μ τ co n ei)

end RibbonOddFinite
#print axioms RibbonOddFinite.pairs_cover
