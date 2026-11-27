import ColorCore
namespace IU

def packed : List Nat → Nat
  | [] => 0
  | a::tail => (2^a) ||| packed tail

theorem packed_mem (L : List Nat) (x : Nat) :
    (packed L).testBit x=true ↔ x∈L := by
  induction L with
  | nil => simp [packed]
  | cons a L ih =>
    simp only [packed,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr ⟨Eq.symm,Eq.symm⟩ Iff.rfl

theorem covered_by_pack {n p q : Nat} {cols : List (List Nat)}
    (e : packed (admissible n p q) = packed cols.flatten) {a : Nat}
    (h : a∈admissible n p q) : a∈cols.flatten := by
  apply (packed_mem _ _).mp
  rw [← e]
  exact (packed_mem _ _).mpr h

theorem prefix_cap_of_pack {n p q : Nat} (cols : List (List Nat))
    (cert : proper n p q cols)
    (pack : packed (admissible n p q)=packed cols.flatten)
    (F : Finset Nat)
    (v : ∀ x∈F, x∈admissible n p q)
    (e : ∀ a∈F, ∀ b∈F, a≠b → edge n p q a b=true) :
    F.card≤cols.length :=
  clique_cap n p q cols cert F (fun a h => covered_by_pack pack (v a h)) e

#print axioms prefix_cap_of_pack
end IU
