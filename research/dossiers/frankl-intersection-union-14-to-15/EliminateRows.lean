import EliminateCore
import FastColor

namespace IU.Eliminate

structure Row (k : Nat) where
  a : Nat
  miss : List (Fin k)

def rowOk {k : Nat} (n p q m : Nat) (colors : Fin k → List Nat)
    (stamp : Nat → Nat) (row : Row k) : Prop :=
  row.miss.Nodup ∧ k - row.miss.length < m ∧
  ∀ i∈row.miss, ∀ b∈colors i,
    b = row.a ∨ stamp b < stamp row.a ∨ edge n p q row.a b = false

instance {k : Nat} (n p q m : Nat) (colors : Fin k → List Nat)
    (stamp : Nat → Nat) (row : Row k) :
    Decidable (rowOk n p q m colors stamp row) := by unfold rowOk; infer_instance

theorem from_row {k : Nat} {n p q m a : Nat} {colors : Fin k → List Nat}
    {stamp : Nat → Nat} {row : Row k} (eq : row.a=a) (ok : rowOk n p q m colors stamp row) :
    ∃ miss : Finset (Fin k), k - miss.card < m ∧
      ∀ i∈miss, ∀ b∈colors i, b ≠ a → stamp a ≤ stamp b → edge n p q a b=false := by
  refine ⟨row.miss.toFinset, ?_, ?_⟩
  · simpa only [List.toFinset_card_of_nodup ok.1] using ok.2.1
  · intro i im b bi nb sb
    rcases ok.2.2 i (List.mem_toFinset.mp im) b bi with H|H|H
    · exact False.elim (nb (H.trans eq))
    · rw [eq] at H
      omega
    · simpa only [eq] using H

theorem row_of_pack {k : Nat} {L : List (Row k)} {a : Nat} {mask : Nat}
    (hm : mask.testBit a=true) (hc : packed (L.map Row.a) = mask) :
    ∃ r∈L, r.a=a :=
  List.mem_map.mp ((packed_mem _ _).mp (hc ▸ hm))

end IU.Eliminate
