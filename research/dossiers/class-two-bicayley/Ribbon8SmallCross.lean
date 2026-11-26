import Ribbon8SmallDescent
import Ribbon8AltAAlgebra
import Ribbon8AltBAlgebra
import Ribbon8AltCAlgebra

namespace Ribbon8Small
open Ribbon5Bridge
variable {G : Type*} [Group G]

def prefix64 (k : Fin 3) : Array P := ![Ribbon8AltA.ww,Ribbon8AltB.ww,Ribbon8AltC.ww] k
def alt128 (k : Fin 3) : Array P := ![Ribbon8AltA.wt,Ribbon8AltB.wt,Ribbon8AltC.wt] k
def altChart (k : Fin 3) : Array Q := ![Ribbon8AltA.tt,Ribbon8AltB.tt,Ribbon8AltC.tt] k

theorem actual_word : ∀ k : Fin 3, word k=alt128 k := by decide +kernel

theorem projected_rows : ∀ k : Fin 3, ∀ i : Fin 128,
    let t := (chart k)[i.val]!
    (t.1,t.2.1,t.2.2.1,t.2.2.2.1)=(altChart k)[i.val]! := by decide +kernel

theorem prefix_exact : ∀ k : Fin 3, (word k).toList.take 64=(prefix64 k).toList :=
  by decide +kernel

theorem prefix_path (x y : G) (k : Fin 3) (i : Nat) (hi : i≤64) :
    pathAt x y (prefix64 k) i=pathAt x y (word k) i := by
  unfold pathAt
  rw [←prefix_exact,List.take_take]
  simp [Nat.min_eq_left hi,Nat.min_eq_right hi]

end Ribbon8Small
#print axioms Ribbon8Small.projected_rows
#print axioms Ribbon8Small.prefix_path
