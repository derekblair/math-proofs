import Ribbon5Packed
import Ribbon5OwnerData

namespace Ribbon5Owner

open Ribbon5Packed
abbrev P := Fin 3
def good (root : Bool) (p : P) (s : State) (prev : P) (n : Nat) : Bool :=
  (ends n s prev).all (fun k => owner root k == p.val)

theorem join (root : Bool) (p : P) (s : State) (prev : P) (n : Nat)
    (H : ∀ j : P, j ≠ back prev → good root p (step s j) j n = true) :
    good root p s prev (n+1) = true := by
  unfold good
  rw [ends,List.all_flatMap,List.all_eq_true]
  intro j _
  by_cases h : j=back prev
  · simp [h]
  · simp only [h,ite_false]
    exact H j h

theorem separates {root : Bool} {p q : P} (ne : p≠q)
    (h : good root p (step (zero root) p) p 15 = true)
    (k : good root q (step (zero root) q) q 15 = true) :
    List.Disjoint
      (ends 15 (step (zero root) p) p)
      (ends 15 (step (zero root) q) q) := by
  intro v hv hw
  have a := beq_iff_eq.mp (List.all_eq_true.mp h v hv)
  have b := beq_iff_eq.mp (List.all_eq_true.mp k v hw)
  exact ne (Fin.ext (a.symm.trans b))

end Ribbon5Owner
#print axioms Ribbon5Owner.join
#print axioms Ribbon5Owner.separates
