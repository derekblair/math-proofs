import Init
namespace BinarySyndromeBits

/-- XOR with the optional sum column is the coordinate syndrome. -/
def syndrome {m : Nat} (selected : Fin m → Bool) (last : Bool) (i : Fin m) : Bool :=
  selected i != last

/-- A vanishing subset selects no nonzero labels or all of them. -/
theorem zero_iff {m : Nat} (selected : Fin m → Bool) (last : Bool) :
    (∀ i, syndrome selected last i=false) ↔
      (last=false ∧ ∀ i, selected i=false) ∨ (last=true ∧ ∀ i, selected i=true) := by
  cases last <;> simp [syndrome]

end BinarySyndromeBits
#print axioms BinarySyndromeBits.zero_iff
