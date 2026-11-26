import Ribbon5Bridge64
import Ribbon5GeneratorDrop
import Ribbon5LawAlgebra
import RibbonClass4Family

namespace Ribbon5Bridge

open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem run_trace (x y : G) (w : List P) (s : Bool×G) :
    (run x y s w).2 = s.2 * Ribbon5Law.trace x y s.1 w := by
  induction w generalizing s with
  | nil => simp [run,Ribbon5Law.trace]
  | cons p t ih =>
    change (run x y (action x y s p) t).2 = s.2 * Ribbon5Law.trace x y s.1 (p::t)
    rw [ih]
    rcases s with ⟨side,z⟩
    cases side <;> fin_cases p <;> simp [action,Ribbon5Law.trace,mul_assoc]

theorem residue_eq (x y : G) :
    residue x y = Ribbon5Law.trace x y false Ribbon5Law.word26 := by
  change (run x y (start G) W).2 = _
  rw [run_trace]
  simp only [start,one_mul]
  rfl

theorem short_close_of_one (nil : LS G 5=⊥) (x y : G) (h : residue x y=1) :
    pathAt x y word32 32=pathAt x y word32 0 := by
  apply Prod.ext
  · rfl
  · have law := Ribbon5Law.law nil x y
    rw [←residue_eq,h,one_pow] at law
    unfold pathAt
    rw [show word32.toList.take 32 = Ribbon5Law.word32 from (by decide +kernel)]
    rw [run_trace]
    simpa [run,start] using law

theorem local_bound (nil : LS G 5=⊥) (x y : G)
    (good : ∀ k : Nat, 1≤k → k≤4 →
      (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portU,map_commutatorElement] using U
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C, portV,map_commutatorElement] using V
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  let F : Bool×G → Bool × (G ⧸ LS G 2) := fun u => (u.1,f u.2)
  by_cases nz : residue x y=1
  · left
    apply cycle_from_at x y word32 (by decide) (short_close_of_one nil x y nz)
    have tr := transported f x y word32 tab32 C cx cy xy (by decide +kernel)
      (fun i hi => step32 ⟨i,hi⟩)
    intro i j le E
    have e : vert (f x) (f y) C tab32[i.val]! = vert (f x) (f y) C tab32[j.val]! :=
      (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
    exact separates_low (f x) (f y) C cx cy xy good _ _ (chart32 i j le) e
  · right
    have cr (z : G) : Commute (residue x y) z := by
      rw [residue_eq]
      exact Ribbon5Law.word26_central nil x y z
    apply cycle_from_at x y word64 (by decide) (full_close x y cr)
    have tr := transported f x y word64 tab64 C cx cy xy (by decide +kernel)
      (fun i hi => step64 ⟨i,hi⟩)
    intro i j le E
    rcases chart64 i j le with s|d
    · have e : vert (f x) (f y) C tab64[i.val]! = vert (f x) (f y) C tab64[j.val]! :=
        (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
      exact separates_low (f x) (f y) C cx cy xy good _ _ s e
    · exact mate_distinct x y cr nz _ _ d E

private theorem generated_bound (nil : LS G 5=⊥) (x y : G) (gen : Generates x y)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  by_cases C : portC x y ∈ LS G 2
  · have h := Ribbon5GeneratorDrop.comm_if_projected_trivial nil x y gen C
    have z : Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 :=
      Ribbon.class2_pair x y (portC x y) (h ▸ Commute.one_left x) (h ▸ Commute.one_left y)
        (ports_xy x y) hx (by simpa only [pow_two] using HaarClass3Odd.odd_no_involution odd hy)
    exact z.imp_right (fun z => z.imp_right Or.inl)
  · have D : (QuotientGroup.mk' (LS G 2) (portC x y))≠1 :=
      fun e => C ((QuotientGroup.eq_one_iff _).mp e)
    have O := HaarClass3Separation64.odd_projection odd
    have Q : ¬3 ∣ Nat.card (G ⧸ LS G 2) :=
      fun t => no3 (dvd_trans t (LS G 2).card_quotient_dvd_card)
    have R := RibbonClass4.root_good_card O Q D
    have good (k : Nat) (a : 1≤k) (b : k≤4) :
        (QuotientGroup.mk' (LS G 2) (portC x y))^k ≠ 1 := by
      interval_cases k
      · simpa only [pow_one] using R.1
      · exact R.2.1
      · exact R.2.2
      · intro eq
        apply HaarClass3Odd.odd_no_involution O R.2.1
        rwa [← pow_mul]
    exact Or.inr (Or.inr (Or.inr (local_bound nil x y good)))

theorem odd_not_three_class5 [Finite G] (nil : LS G 5=⊥) (x y : G)
    (odd : Odd (Nat.card G)) (no3 : ¬3 ∣ Nat.card G) (hx : x≠1) (hy : y≠1) :
    Ribbon.Cycle x y 4 ∨ Ribbon.Cycle x y 8 ∨ Ribbon.Cycle x y 16 ∨
      Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let S := Pair x y
  have dvd : Nat.card S ∣ Nat.card G := S.card_subgroup_dvd_card
  have hx' : leftPort x y≠1 := fun e => hx (congrArg Subtype.val e)
  have hy' : rightPort x y≠1 := fun e => hy (congrArg Subtype.val e)
  rcases generated_bound (pair_nil x y 5 nil) _ _ (pair_generates x y)
      (Odd.of_dvd_nat odd dvd) (fun t => no3 (dvd_trans t dvd)) hx' hy' with h|h|h|h|h
  · exact Or.inl (pair_lift x y 4 h)
  · exact Or.inr (Or.inl (pair_lift x y 8 h))
  · exact Or.inr (Or.inr (Or.inl (pair_lift x y 16 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_lift x y 32 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_lift x y 64 h))))

end Ribbon5Bridge
#print axioms Ribbon5Bridge.local_bound
#print axioms Ribbon5Bridge.odd_not_three_class5
