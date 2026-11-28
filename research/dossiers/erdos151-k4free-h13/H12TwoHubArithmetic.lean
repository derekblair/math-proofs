import Mathlib.Data.Finset.Card

namespace Erdos151H12

def alphaFloor (m : Nat) : Nat :=
  if 9 ≤ m then 4 else if 6 ≤ m then 3 else if 3 ≤ m then 2 else if 1 ≤ m then 1 else 0

def eligibleFloor (r c : Nat) : Nat := max 1 (alphaFloor (r-1-c))

def twoHubFloor (r s c : Nat) : Nat := c + eligibleFloor r c + eligibleFloor s c

theorem twoHubFloor_ge_six (r s c : Nat) (hr : 8 ≤ r) (hs : 8 ≤ s) (hc : 2 ≤ c) :
    6 ≤ twoHubFloor r s c := by
  unfold twoHubFloor eligibleFloor alphaFloor
  repeat' first | split | omega

theorem twoHubFloor_le_six (r s c : Nat) (hr : 8 ≤ r) (hs : 8 ≤ s) (hc : 2 ≤ c)
    (h : twoHubFloor r s c ≤ 6) :
    c = 2 ∧ r = 8 ∧ s = 8 := by
  unfold twoHubFloor eligibleFloor alphaFloor at h
  repeat' first | split at h | omega

theorem twoHubFloor_le_seven (r s c : Nat) (hr : 8 ≤ r) (hs : 8 ≤ s) (hc : 2 ≤ c)
    (h : twoHubFloor r s c ≤ 7) :
    (c = 2 ∧ (r = 8 ∨ s = 8)) ∨
    (c = 3 ∧ r ≤ 9 ∧ s ≤ 9) ∨ (c = 5 ∧ r = 8 ∧ s = 8) := by
  unfold twoHubFloor eligibleFloor alphaFloor at h
  repeat' first | split at h | omega

theorem nonadjacent_overlap_cut (n r s c : Nat) (hr : 8 ≤ r) (hs : 8 ≤ s)
    (h : c + alphaFloor (r+s-c) + n ≤ 64) (hn : 53 ≤ n) :
    (n = 53 → c ≤ 8) ∧ (n = 54 → c ≤ 6) ∧ (n = 55 → c ≤ 5) := by
  unfold alphaFloor at h
  repeat' first | split at h | omega

/-- A (d=10) row includes a pool of ≤10 possible owners and is at most q=20
single-lone cases; one owner may contribute TWO single-lone cases in H=12. -/
theorem degreeTen_deficit (a b c d ell : Nat) (ha : a ≤ 20)
    (hp : 5*a+4*b+5*c ≤ 100) (he : a+c+2*d ≤ ell) :
    4*(2*a+b+c+d) ≤ 120 + 2*ell := by
  omega

theorem degreeTen_endpoints (r e I z IU a b c d ell : Nat)
    (hz : z ≤ 3) (hUT : z = 3 → 6 ≤ IU) (hUf : z = 2 → IU = 0 ∨ 1 ≤ IU)
    (ha : a ≤ 20) (hp : 5*a+4*b+5*c ≤ 100)
    (hl : a+c+2*d ≤ ell) (hSlots : ell + 7*r ≤ 100)
    (hLower : 3*42 + IU ≤ I + 3*z + (2*a+b+c+d))
    (hUpper : I + 2*e ≤ 100) :
    (r = 10 → e ≤ 14) ∧
    (r = 9 → 14 ≤ e → z = 2 ∧ IU = 0 ∧ e = 14 ∧ I = 72 ∧
      ((a = 19 ∧ b = 1 ∧ c = 0 ∧ d = 9) ∨ (a = 20 ∧ b = 0 ∧ c = 0 ∧ d = 8))) := by
  have hex : 4*(2*a+b+c+d) ≤ 100 + a + 2*ell - 3*c := by omega
  have hd := degreeTen_deficit a b c d ell ha hp hl
  constructor
  · intro h; omega
  · intro hr he
    have hZ : z = 2 := by
      by_cases hg : z = 3
      · have := hUT hg
        omega
      · omega
    have hu : IU = 0 := by
      rcases hUf hZ with h | h
      · exact h
      · omega
    have hh : 48 ≤ 2*a+b+c+d := by omega
    have a' : 18 ≤ a := by omega
    have c' : c = 0 := by omega
    refine ⟨hZ,hu,by omega,by omega,?_⟩
    by_cases h18 : a = 18
    · omega
    · by_cases h19 : a = 19
      · left; omega
      · right; omega

#print axioms twoHubFloor_ge_six
#print axioms twoHubFloor_le_six
#print axioms twoHubFloor_le_seven
#print axioms nonadjacent_overlap_cut
#print axioms degreeTen_deficit
#print axioms degreeTen_endpoints
end Erdos151H12
