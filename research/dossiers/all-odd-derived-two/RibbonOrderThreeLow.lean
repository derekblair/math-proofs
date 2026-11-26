import RibbonStationaryWordGraph
import Mathlib.Data.ZMod.Basic

namespace RibbonOrderThree
open RibbonStationaryWord Ribbon5Bridge HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 20000
set_option maxHeartbeats 0

abbrev W3 := Fin 3
def wid : W3 → Count := ![0,2,3]
def ell (k : W3) : Array Q :=
  ((spec (wid k)).T.scanl push (false,0,0,0)).toArray

theorem ell_size : ∀ k : W3, (ell k).size=65 := by decide +kernel
theorem ell_start : ∀ k : W3, (ell k)[0]! = (false,0,0,0) := by decide +kernel
theorem ell_step : ∀ (k : W3) (i : Fin 64),
    push (ell k)[i.val]! (spec (wid k)).T.toArray[i.val]! = (ell k)[i.val+1]! := by
  decide +kernel
theorem ell_range : ∀ (k : W3) (i j : Fin 64),
    Int.natAbs ((ell k)[i.val]!.2.1-(ell k)[j.val]!.2.1)≤2 ∧
    Int.natAbs ((ell k)[i.val]!.2.2.1-(ell k)[j.val]!.2.2.1)≤2 := by decide +kernel

def lowKey (k : W3) (i : Fin 64) : Bool×ℤ×ℤ×ZMod 3 :=
  let q := (ell k)[i.val]!
  (q.1,q.2.1,q.2.2.1,q.2.2.2)

theorem short_same (c : G) (o : orderOf c=3) {s t : ℤ}
    (h : (s-t).natAbs≤2) (eq : c^s=c^t) : s=t := by
  have v : c^(s-t)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  have w := orderOf_dvd_iff_zpow_eq_one.mpr v
  rw [o] at w
  have z : (3:ℤ)∣s-t := w
  obtain ⟨j,hj⟩ := z
  omega

theorem low_equal (x y c : G) (o : orderOf c=3) (cx : Commute c x) (cy : Commute c y)
    (xy : x*y=y*x*c) (u v : Q)
    (h : (u.2.1-v.2.1).natAbs≤2 ∧ (u.2.2.1-v.2.2.1).natAbs≤2)
    (E : vert x y c u=vert x y c v) :
    (u.1,u.2.1,u.2.2.1,(u.2.2.2 : ZMod 3))=(v.1,v.2.1,v.2.2.1,(v.2.2.2 : ZMod 3)) := by
  have side := congrArg (Prod.fst : Bool×G→Bool) E
  have EQ : HaarCycle.norm x y c u.2=HaarCycle.norm x y c v.2 := congrArg Prod.snd E
  have K := HaarBound16.conjugate_eq x y c cx cy xy EQ
  have I := short_same c o h.1 K.1
  have J := short_same c o h.2 K.2
  unfold HaarCycle.norm at EQ
  rw [I,J] at EQ
  have eq : c^(u.2.2.2-v.2.2.2)=1 := by rw [zpow_sub,mul_left_cancel EQ,mul_inv_cancel]
  have dv := orderOf_dvd_iff_zpow_eq_one.mpr eq
  rw [o] at dv
  have C : (u.2.2.2 : ZMod 3)=(v.2.2.2 : ZMod 3) := by
    rw [←sub_eq_zero,←Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 dv
  exact Prod.ext side (Prod.ext I (Prod.ext J C))

theorem projected_sound (x y : G) (k : W3) (i j : Fin 64)
    (o : orderOf (QuotientGroup.mk' (LS G 2) (portC x y))=3)
    (e : pathAt x y (spec (wid k)).T.toArray i.val =
        pathAt x y (spec (wid k)).T.toArray j.val) :
    lowKey k i=lowKey k j := by
  let f := QuotientGroup.mk' (LS G 2)
  let C := f (portC x y)
  have U' : f (portU x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have V' : f (portV x y)=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have cx : Commute C (f x) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portU,map_commutatorElement] using U'
  have cy : Commute C (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [C,portV,map_commutatorElement] using V'
  have xy : f x*f y=f y*f x*C := by simpa only [C,map_mul] using congrArg f (ports_xy x y)
  have len : (spec (wid k)).T.toArray.size=64 := by simpa only [List.size_toArray] using (all_valid (wid k)).1
  have tr := transported f x y (spec (wid k)).T.toArray (ell k) C cx cy xy (ell_start k)
    (fun n hn => ell_step k ⟨n,by rwa [len] at hn⟩)
  have hi : i.val≤(spec (wid k)).T.toArray.size := by rw [len]; omega
  have hj : j.val≤(spec (wid k)).T.toArray.size := by rw [len]; omega
  have E := (tr i.val hi).symm.trans ((congrArg (fun u : Bool×G => (u.1,f u.2)) e).trans (tr j.val hj))
  exact low_equal (f x) (f y) C o cx cy xy _ _ (ell_range k i j) E

end RibbonOrderThree
#print axioms RibbonOrderThree.projected_sound
