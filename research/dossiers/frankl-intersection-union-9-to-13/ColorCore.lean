import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

namespace IU
def rank (m t : Nat) : Nat :=
  ((List.range t).filter (fun i => m.testBit i)).length

def edge (n p q a b : Nat) : Bool :=
  let t := max p (rank a n + rank b n - (n-q))
  (List.range (n+1)).any fun k => decide (t + k ≤ rank a k + rank b k)

def vertex (n p q a : Nat) : Bool :=
    decide (p ≤ rank a n ∧ rank a n ≤ n-q) && edge n p q a a

def admissible (n p q : Nat) : List Nat :=
  (List.range (2^n)).filter (vertex n p q)

def proper (n p q : Nat) (paint : List (List Nat)) : Prop :=
  ∀ cls ∈ paint, cls.Pairwise (fun a b => edge n p q a b = false)

instance (n p q : Nat) (paint : List (List Nat)) : Decidable (proper n p q paint) := by
  unfold proper
  infer_instance

private theorem between_of_pairwise {R : Nat → Nat → Prop} {L : List Nat}
    (ok : L.Pairwise R) {a b : Nat} (A : a ∈ L) (B : b ∈ L) (N : a≠b) :
    R a b ∨ R b a := by
  induction L with
  | nil => simp at A
  | cons x L ih =>
    have H := List.pairwise_cons.mp ok
    rcases List.mem_cons.mp A with (rfl|aa) <;> rcases List.mem_cons.mp B with (rfl|bb)
    · exact False.elim (N rfl)
    · exact Or.inl (H.1 _ bb)
    · exact Or.inr (H.1 _ aa)
    · exact ih H.2 aa bb

theorem clique_cap (n p q : Nat) (L : List (List Nat)) (ok : proper n p q L)
    (F : Finset Nat)
    (hv : ∀ a ∈ F, a ∈ L.flatten)
    (edgeF : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → edge n p q a b = true) :
    F.card ≤ L.length := by
  classical
  revert ok F
  induction L with
  | nil =>
    intro ok F hv edgeF
    have le : F ⊆ ∅ := fun a ha => False.elim (by simpa using hv a ha)
    simpa using Finset.card_le_card le
  | cons c L ih =>
    intro ok F hv edgeF
    let Fc := F.filter (· ∈ c)
    let Fr := F.filter (· ∉ c)
    have fc : Fc.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have A := Finset.mem_filter.mp ha
      have B := Finset.mem_filter.mp hb
      by_contra e
      have cl := ok c List.mem_cons_self
      have N : edge n p q a b = false ∨ edge n p q b a = false := by
        exact between_of_pairwise cl A.2 B.2 e
      rcases N with Z|Z
      · rw [edgeF a A.1 b B.1 e] at Z
        contradiction
      · rw [edgeF b B.1 a A.1 (Ne.symm e)] at Z
        contradiction
    have fr : Fr.card ≤ L.length := by
      apply ih (fun k hk => ok k (List.mem_cons_of_mem _ hk)) Fr
      · intro a ha
        have A := Finset.mem_filter.mp ha
        simpa only [List.flatten_cons,List.mem_append,or_iff_right A.2] using hv a A.1
      · intro a ha b hb ne
        exact edgeF a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 ne
    have parts : Fc.card+Fr.card=F.card := Finset.card_filter_add_card_filter_not (s := F) (· ∈ c)
    simp only [List.length_cons]
    omega

#print axioms clique_cap
end IU
