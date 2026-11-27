import Mathlib.Tactic

namespace SignedPermanentMaskCertificate

abbrev Entry := Fin 4 × Fin 4
abbrev Matching := Fin 4 → Fin 4

def u0123 : Matching := ![0, 1, 2, 3]
def u0132 : Matching := ![0, 1, 3, 2]
def u0213 : Matching := ![0, 2, 1, 3]
def u0231 : Matching := ![0, 2, 3, 1]
def u0312 : Matching := ![0, 3, 1, 2]
def u0321 : Matching := ![0, 3, 2, 1]

def multiplicity (ms : List Matching) (e : Entry) : ℕ :=
  (ms.filter fun m => decide (m e.1 = e.2)).length

/-- Equality of exponent vectors for the two products of three matchings. -/
theorem cubic_edge_multiplicity :
    ∀ e : Entry,
      multiplicity [u0132, u0213, u0321] e =
      multiplicity [u0123, u0231, u0312] e := by
  decide

def rankBudget (a b : ℕ) : ℕ :=
  a + b + (3 - a) * (if 2 ≤ b then 3 else 2) +
    (3 - b) * (if 2 ≤ a then 3 else 2)

/-- Combinatorial budget with a rank floor of three when two rank-one cosets are
    opposite. The abstract Gram-to-rank-floor argument is not formalized here. -/
theorem candidates_exact :
    (List.finRange 4).flatMap
      (fun a => ((List.finRange 4).map fun b =>
        (a.val, b.val, rankBudget a.val b.val)).filter fun x => decide (x.2.2 ≤ 10)) =
    [(1,1,10), (1,3,10), (2,2,10), (2,3,8), (3,1,10), (3,2,8), (3,3,6)] := by
  decide

#print axioms cubic_edge_multiplicity
#print axioms candidates_exact

end SignedPermanentMaskCertificate
