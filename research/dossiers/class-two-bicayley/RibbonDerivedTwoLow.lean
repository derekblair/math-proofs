import RibbonDerivedTwoClose
namespace RibbonDerivedTwo
open HaarClass4Structure HaarClass4Generate HaarClass4Ports RibbonClass4Fallback Ribbon5Bridge Ribbon6
open scoped commutatorElement
variable {G : Type*} [Group G]
theorem local_bound (m : D2 G) (x y : G)
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
  by_cases nz : Ribbon6.residue x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,nz]; rfl)
    have tr := transported f x y wa ta C cx cy xy (by decide +kernel)
      (fun i hi => astep ⟨i,hi⟩)
    intro i j le E
    have e : vert (f x) (f y) C ta[i.val]! = vert (f x) (f y) C ta[j.val]! :=
      (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
    exact separates_low (f x) (f y) C cx cy xy good _ _ (achart i j le) e
  · right
    apply cycle_from_at x y wc (by decide) (RibbonDerivedTwo.close m x y)
    have tr := transported f x y wc tc C cx cy xy (by decide +kernel)
      (fun i hi => cstep ⟨i,hi⟩)
    intro i j le E
    rcases cchart i j le with s|d
    · have e : vert (f x) (f y) C tc[i.val]! = vert (f x) (f y) C tc[j.val]! :=
        (tr i.val i.isLt.le).symm.trans ((congrArg F E).trans (tr j.val j.isLt.le))
      exact separates_low (f x) (f y) C cx cy xy good _ _ s e
    · exact mate_sep x y nz _ _ d E

end RibbonDerivedTwo
#print axioms RibbonDerivedTwo.local_bound
