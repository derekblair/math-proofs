import HaarClass3Collector64
import HaarClass3Separation64

namespace RibbonClass3Data

open HaarClass3Table HaarClass3Collector64
open HaarClass3Separation64 (i j k a b small)

def base : Coord := (0,0,0,0,0)
def signs (pickU : Bool) (n : Nat) : Bool :=
  if pickU then (#[true,true,true,true,false,false,false,true,true,false,true,false,false,true,false,false] : Array Bool)[n]!
  else (#[true,true,true,true,false,false,true,false,false,true,false,true,true,false,false,false] : Array Bool)[n]!

def port (n : Nat) : Fin 3 := if n%2=0 then 1 else 2

def row (pickU : Bool) : Nat → Coord
  | 0 => base
  | n+1 => move (signs pickU n) (port n) (row pickU n)

def P (pickU : Bool) (t : Fin 16) : Coord := row pickU t.val

instance (n : ℤ) : Decidable (Range n) := by unfold Range; infer_instance

theorem range : ∀ (pickU : Bool) (t : Fin 16), Range (P pickU t).1 := by decide +kernel
theorem closed : ∀ pickU : Bool, row pickU 16=base := by decide +kernel

instance (n : ℤ) : Decidable (small n) := by unfold small; infer_instance

theorem i_bound : ∀ (pickU : Bool) (r s : Fin 16), i (P pickU r) ≠ i (P pickU s) →
    small (i (P pickU r)-i (P pickU s)) := by decide +kernel

theorem j_bound : ∀ (pickU : Bool) (r s : Fin 16), j (P pickU r) ≠ j (P pickU s) →
    small (j (P pickU r)-j (P pickU s)) := by decide +kernel

theorem k_bound : ∀ (pickU : Bool) (r s : Fin 16), i (P pickU r)=i (P pickU s) →
    j (P pickU r)=j (P pickU s) → k (P pickU r) ≠ k (P pickU s) →
      small (k (P pickU r)-k (P pickU s)) := by decide +kernel

def ClashFree (pickU : Bool) (p q : Coord) : Prop :=
  small (i p-i q) ∨ small (j p-j q) ∨ small (k p-k q) ∨
    (if pickU then (a q-a p=1 ∨ a q-a p= -1) ∧ b q-b p=0
    else (b q-b p=1 ∨ b q-b p= -1) ∧ a q-a p=0)

instance (pickU : Bool) (p q : Coord) : Decidable (ClashFree pickU p q) := by
  unfold ClashFree small
  split <;> infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem collision : ∀ (pickU : Bool) (r s : Fin 16), r≠s →
    ClashFree pickU (P pickU r) (P pickU s) := by decide +kernel

end RibbonClass3Data
#print axioms RibbonClass3Data.collision
