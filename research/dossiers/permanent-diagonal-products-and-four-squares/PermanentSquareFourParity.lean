import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace PermanentSquareFour

def certificate : List (List Nat) := [[0,1,6,7],[0,5,14,16],[1,4,15,17],[2,3,12,13],[2,4,8,10],[3,5,9,11],[6,11,12,17],[7,10,13,16],[8,9,14,15]]

theorem odd_number_even_incidence :
    certificate.length % 2 = 1 ∧
      ∀ i : Fin 24, certificate.flatten.count i.val % 2 = 0 := by
  decide +kernel

/-- The nine sign constraints cannot all hold: each variable occurs an even
    number of times and their right sides sum to one in characteristic two. -/
theorem impossible_sign_assignment (s : Fin 24 → ZMod 2)
    (h0 : s 0 + s 1 + s 6 + s 7 = 1)
    (h1 : s 0 + s 5 + s 14 + s 16 = 1)
    (h2 : s 1 + s 4 + s 15 + s 17 = 1)
    (h3 : s 2 + s 3 + s 12 + s 13 = 1)
    (h4 : s 2 + s 4 + s 8 + s 10 = 1)
    (h5 : s 3 + s 5 + s 9 + s 11 = 1)
    (h6 : s 6 + s 11 + s 12 + s 17 = 1)
    (h7 : s 7 + s 10 + s 13 + s 16 = 1)
    (h8 : s 8 + s 9 + s 14 + s 15 = 1) :
    False := by
  have hh : (s 0 + s 1 + s 6 + s 7) + (s 0 + s 5 + s 14 + s 16) + (s 1 + s 4 + s 15 + s 17) + (s 2 + s 3 + s 12 + s 13) + (s 2 + s 4 + s 8 + s 10) + (s 3 + s 5 + s 9 + s 11) + (s 6 + s 11 + s 12 + s 17) + (s 7 + s 10 + s 13 + s 16) + (s 8 + s 9 + s 14 + s 15) = 1 := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    decide
  ring_nf at hh
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [htwo] at hh

#print axioms odd_number_even_incidence
#print axioms impossible_sign_assignment

end PermanentSquareFour
