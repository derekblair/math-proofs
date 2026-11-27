import HaarMetaS025Voltage
import HaarMetaVoltagePullback
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card

namespace HaarMetaS025Geometry
open HaarMetaS025Voltage HaarMetaVoltagePullback
variable {G Q : Type*} [Group G] [Group Q]

def ix (u : B) : Fin 13 := ⟨u.val%13,by omega⟩
def side (u : B) : Bool := decide (13≤u.val)
def off (j : Fin 3) : ℕ := ![0,2,5] j

theorem geoflip : ∀ u j, u≠next u j → side (next u j)= !side u := by decide +kernel
theorem georev : ∀ u j, u≠next u j → next (next u j) j=u := by decide +kernel
theorem geounique : ∀ u j k, u≠next u j → next u j=next u k → j=k := by decide +kernel
theorem geopow : ∀ u j, u≠next u j → side u=false →
    (ix (next u j)).val=(ix u).val+off j := by decide +kernel

def setup (f : G→*Q) (x y z : G) (px : f x=(f z)^(2:ℕ)) (py : f y=(f z)^(5:ℕ))
    (inj : Function.Injective (fun t : Fin 13 => f (z^t.val))) : Setup f x y B := by
  refine ⟨next,side,fun u => z^(ix u).val,?_,geoflip,georev,geounique,?_⟩
  · intro u v e
    have s : side u=side v := congrArg Prod.fst e
    have q : f (z^(ix u).val)=f (z^(ix v).val) := congrArg Prod.snd e
    have h := congrArg Fin.val (inj q)
    change u.val%13=v.val%13 at h
    apply Fin.ext
    unfold side at s
    by_cases hu : 13≤u.val
    · have hv : 13≤v.val := by simpa [hu] using s.symm
      omega
    · have hv : ¬13≤v.val := by simpa [hu] using s.symm
      omega
  · intro u j ne hs
    have h := geopow u j ne hs
    change f (z^(ix (next u j)).val)=f (z^(ix u).val)*f (HaarMetaVoltagePullback.port x y j)
    rw [map_pow,map_pow,h,pow_add]
    fin_cases j <;> simp [HaarMetaVoltagePullback.port,off,px,py]

theorem inject_of_order (f : G→*Q) (z : G) (large : 13≤orderOf (f z)) :
    Function.Injective (fun t : Fin 13 => f (z^t.val)) := by
  intro a b e
  apply Fin.ext
  have ha : a.val ∈ Set.Iio (orderOf (f z)) := lt_of_lt_of_le a.isLt large
  have hb : b.val ∈ Set.Iio (orderOf (f z)) := lt_of_lt_of_le b.isLt large
  exact pow_injOn_Iio_orderOf ha hb (by simpa only [map_pow] using e)

end HaarMetaS025Geometry
#print axioms HaarMetaS025Geometry.setup
