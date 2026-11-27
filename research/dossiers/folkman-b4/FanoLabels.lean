import BookConclusion
import Mathlib.Data.Fin.VecNotation

namespace FolkmanB4.Fano
open Finset

def line : Fin 7 → Finset (Fin 7) :=
  ![{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}]

def inc (l p : Fin 7) : Prop := p∈line l
instance : DecidableRel inc := fun _ _ => inferInstanceAs (Decidable (_∈_))

def pointCycle : Equiv.Perm (Fin 7) :=
  ⟨![1,3,5,2,0,6,4],![4,0,3,1,6,2,5],by decide,by decide⟩

def lineCycle : Equiv.Perm (Fin 7) :=
  ⟨![3,0,4,5,1,6,2],![1,4,6,0,2,3,5],by decide,by decide⟩

theorem cycle_preserves : ∀ l p : Fin 7, inc (lineCycle l) (pointCycle p) ↔ inc l p := by decide

theorem powers_preserve (k : Nat) (l p : Fin 7) :
    inc ((lineCycle^k) l) ((pointCycle^k) p) ↔ inc l p := by
  induction k with
  | zero => simp [Equiv.Perm.one_apply]
  | succ n ih =>
    rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,cycle_preserves,ih]

theorem can_pin_column : ∀ c : Fin 7, ∃ k : Fin 7, (pointCycle^k.val) 6 = c := by decide
theorem can_pin_row : ∀ r : Fin 7, ∃ k : Fin 7, (lineCycle^k.val) 0 = r := by decide

theorem canonical_card : ∀ l : Fin 7, (line l).card=3 := by decide

#print axioms powers_preserve
#print axioms can_pin_column
#print axioms can_pin_row
end FolkmanB4.Fano
