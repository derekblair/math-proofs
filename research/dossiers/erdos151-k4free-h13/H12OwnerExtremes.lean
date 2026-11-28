import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos151H12
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

theorem twenty_every_owner_two (S : Finset V) (a : V → Nat) (hS : S.card=10)
    (hLocal : ∀ v∈S, a v≤2) (hSum : 20 ≤ ∑ v∈S,a v) (v : V) (hv : v∈S) :
    a v = 2 := by
  have he : (S.erase v).card = 9 := by
    have := Finset.card_erase_add_one hv
    omega
  have ht := Finset.sum_le_sum (s := S.erase v) (fun x hx => hLocal x (Finset.mem_of_mem_erase hx))
  have hUpper : (∑ x ∈ S.erase v,a x) ≤ 18 := by simpa [he] using ht
  have hx := Finset.sum_erase_add (a := v) (f := a) S hv
  have ha := hLocal v hv
  omega

theorem nineteen_not_two_available (S : Finset V) (a : V → Nat) (hS : S.card=10)
    (hLocal : ∀ v∈S, a v≤2) (hSum : 19 ≤ ∑ v∈S,a v)
    (u v : V) (hu : u∈S) (hv : v∈S) (hne : u≠v) (hU : a u≤1) (hV : a v≤1) :
    False := by
  have hv' : v∈S.erase u := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
  have he : ((S.erase u).erase v).card = 8 := by
    have := Finset.card_erase_add_one hu
    have := Finset.card_erase_add_one hv'
    omega
  have ht := Finset.sum_le_sum (s := (S.erase u).erase v)
    (fun x hx => hLocal x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
  have hUpper : (∑ x ∈ (S.erase u).erase v,a x) ≤ 16 := by simpa [he] using ht
  have hx := Finset.sum_erase_add (a := u) (f := a) S hu
  have hy := Finset.sum_erase_add (a := v) (f := a) (S.erase u) hv'
  omega

#print axioms twenty_every_owner_two
#print axioms nineteen_not_two_available
end Erdos151H12
