import HaarMetaS013Voltage
import HaarMetaVoltagePullback
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card

namespace HaarMetaS013Geometry
open HaarMetaS013Voltage HaarMetaVoltagePullback
variable {G Q : Type*} [Group G] [Group Q]

def ix (u : B) : Fin 10 := ⟨u.val%10,by omega⟩
def side (u : B) : Bool := decide (10≤u.val)
def off (j : Fin 3) : ℕ := ![0,1,3] j

theorem geoflip : ∀ u j, u≠next u j → side (next u j)= !side u := by decide +kernel
theorem georev : ∀ u j, u≠next u j → next (next u j) j=u := by decide +kernel
theorem geounique : ∀ u j k, u≠next u j → next u j=next u k → j=k := by decide +kernel
theorem geopow : ∀ u j, u≠next u j → side u=false →
    (ix (next u j)).val=(ix u).val+off j := by decide +kernel

def setup (f : G→*Q) (x y z : G) (px : f x=(f z)^(1:ℕ)) (py : f y=(f z)^(3:ℕ))
    (inj : Function.Injective (fun t : Fin 10 => f (z^t.val))) : Setup f x y B := by
  refine ⟨next,side,fun u => z^(ix u).val,?_,geoflip,georev,geounique,?_⟩
  · intro u v e
    have s : side u=side v := congrArg Prod.fst e
    have q : f (z^(ix u).val)=f (z^(ix v).val) := congrArg Prod.snd e
    have h := congrArg Fin.val (inj q)
    change u.val%10=v.val%10 at h
    apply Fin.ext
    unfold side at s
    by_cases hu : 10≤u.val
    · have hv : 10≤v.val := by simpa [hu] using s.symm
      omega
    · have hv : ¬10≤v.val := by simpa [hu] using s.symm
      omega
  · intro u j ne hs
    have h := geopow u j ne hs
    change f (z^(ix (next u j)).val)=f (z^(ix u).val)*f (HaarMetaVoltagePullback.port x y j)
    rw [map_pow,map_pow,h,pow_add]
    fin_cases j <;> simp [HaarMetaVoltagePullback.port,off,px,py]

theorem inject_of_order (f : G→*Q) (z : G) (large : 10≤orderOf (f z)) :
    Function.Injective (fun t : Fin 10 => f (z^t.val)) := by
  intro a b e
  apply Fin.ext
  have ha : a.val ∈ Set.Iio (orderOf (f z)) := lt_of_lt_of_le a.isLt large
  have hb : b.val ∈ Set.Iio (orderOf (f z)) := lt_of_lt_of_le b.isLt large
  exact pow_injOn_Iio_orderOf ha hb (by simpa only [map_pow] using e)

end HaarMetaS013Geometry
#print axioms HaarMetaS013Geometry.setup
