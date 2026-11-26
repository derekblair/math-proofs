import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic

/-!
# Graph Brain Project open lower bound #47 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 47th of the 89 lower bounds in the issue body:

> For connected graphs:
> `independence_number(x) >= card_cut_vertices(x) + card_pendants(x) - matching_number(x)`

Counterexample: graph6 `H?`D@`a` (9 vertices, 9 edges): the triangle `2-6-8` with the pendant
paths `6-0-4`, `8-1-5`, `2-7-3`. Cut vertices `{0,1,2,6,7,8}` (6), pendants `{3,4,5}` (3),
matching number `4` (≤ ⌊9/2⌋), `α = 4`; RHS `= 6 + 3 - 4 = 5 > 4`.
(For trees the bound is tight by König's theorem; one triangle breaks it.)
-/

namespace GBP421_047

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `v` is a cut vertex: some two other vertices are separated by `v`
(every walk between them passes through `v`). -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.Reachable a b ∧ ∀ p : G.Walk a b, v ∈ p.support

open Classical in
noncomputable def cardCutVertices (G : SimpleGraph V) : ℕ := #(univ.filter (IsCutVertex G))

def cardPendants (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  #(univ.filter fun v => G.degree v = 1)

/-- A matching of size `k`: `k` edges `(f i).1 (f i).2` whose `2k` endpoints are distinct. -/
def IsMatchingOfSize (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V × V, (∀ i, G.Adj (f i).1 (f i).2) ∧
    Function.Injective (Sum.elim (fun i => (f i).1) (fun i => (f i).2))

/-- The matching number. -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ := sSup {k | IsMatchingOfSize G k}

/-- GBP #421 lower bound #47. -/
def Conjecture47 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      (cardCutVertices G : ℝ) + cardPendants G - matchingNumber G ≤ G.indepNum

omit [DecidableEq V] in
lemma matchingNumber_le (G : SimpleGraph V) : 2 * matchingNumber G ≤ Fintype.card V := by
  have hle : ∀ k ∈ {k | IsMatchingOfSize G k}, 2 * k ≤ Fintype.card V := by
    rintro k ⟨f, -, hf⟩
    have := Fintype.card_le_of_injective _ hf
    simpa [Fintype.card_sum, two_mul] using this
  have hne : ({k | IsMatchingOfSize G k} : Set ℕ).Nonempty :=
    ⟨0, fun i => i.elim0, fun i => i.elim0, fun x => by rcases x with x | x <;> exact x.elim0⟩
  have hbdd : BddAbove {k | IsMatchingOfSize G k} :=
    ⟨Fintype.card V, fun k hk => by have := hle k hk; omega⟩
  obtain ⟨k, hk, hks⟩ : sSup {k | IsMatchingOfSize G k} ∈ {k | IsMatchingOfSize G k} :=
    Nat.sSup_mem hne hbdd
  exact hle _ ⟨k, hk, hks⟩

omit [Fintype V] [DecidableEq V] in
/-- Separation lemma: if `S` contains `a`, not `b`, and every edge leaving `S` ends at `v`,
then every walk from `a` to `b` visits `v`. -/
lemma mem_support_of_sep (G : SimpleGraph V) (v : V) (S : Set V)
    (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y = v) :
    ∀ {a b : V} (p : G.Walk a b), a ∈ S → b ∉ S → v ∈ p.support := by
  intro a b p
  induction p with
  | nil => intro h1 h2; exact absurd h1 h2
  | cons h p ih =>
    intro ha hb
    rcases hS _ ha _ h with hc | rfl
    · exact List.mem_cons_of_mem _ (ih hc hb)
    · exact List.mem_cons_of_mem _ p.start_mem_support

/-! ### The counterexample -/

def edges : List (Fin 9 × Fin 9) :=
  [(0, 4), (0, 6), (1, 5), (1, 8), (2, 6), (2, 7), (2, 8), (3, 7), (6, 8)]

def G : SimpleGraph (Fin 9) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 9, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r6 : G.Reachable 2 6 := a 2 6 (by decide)
  have r8 : G.Reachable 2 8 := a 2 8 (by decide)
  have r7 : G.Reachable 2 7 := a 2 7 (by decide)
  have r0 : G.Reachable 2 0 := r6.trans (a 6 0 (by decide))
  have r1 : G.Reachable 2 1 := r8.trans (a 8 1 (by decide))
  have h : ∀ v : Fin 9, G.Reachable 2 v := by
    intro v
    fin_cases v
    · exact r0
    · exact r1
    · exact Reachable.refl _
    · exact r7.trans (a 7 3 (by decide))
    · exact r0.trans (a 0 4 (by decide))
    · exact r1.trans (a 1 5 (by decide))
    · exact r6
    · exact r7
    · exact r8
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

/-- Certificate `(v, a, b, S)`: `S` contains `a`, not `b`, not `v`, closed except through `v`. -/
lemma cut_cert (v a b : Fin 9) (S : Finset (Fin 9)) (hav : a ≠ v) (hbv : b ≠ v)
    (ha : a ∈ S) (hb : b ∉ S) (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S ∨ y = v) :
    IsCutVertex G v :=
  ⟨a, b, hav, hbv, G_connected.preconnected a b,
    fun p => mem_support_of_sep G v (S : Set (Fin 9)) (by simpa using hS) p (by simpa using ha)
      (by simpa using hb)⟩

lemma cut0 : IsCutVertex G 0 := cut_cert 0 4 6 {4} (by decide) (by decide) (by decide) (by decide) (by decide)
lemma cut6 : IsCutVertex G 6 := cut_cert 6 0 2 {0, 4} (by decide) (by decide) (by decide) (by decide) (by decide)
lemma cut1 : IsCutVertex G 1 := cut_cert 1 5 8 {5} (by decide) (by decide) (by decide) (by decide) (by decide)
lemma cut8 : IsCutVertex G 8 := cut_cert 8 1 2 {1, 5} (by decide) (by decide) (by decide) (by decide) (by decide)
lemma cut7 : IsCutVertex G 7 := cut_cert 7 3 2 {3} (by decide) (by decide) (by decide) (by decide) (by decide)
lemma cut2 : IsCutVertex G 2 := cut_cert 2 7 6 {7, 3} (by decide) (by decide) (by decide) (by decide) (by decide)

lemma six_le_cut : 6 ≤ cardCutVertices G := by
  classical
  unfold cardCutVertices
  have : ({0, 1, 2, 6, 7, 8} : Finset (Fin 9)) ⊆ univ.filter (IsCutVertex G) := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    simp only [mem_filter, mem_univ, true_and]
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cut0
    · exact cut1
    · exact cut2
    · exact cut6
    · exact cut7
    · exact cut8
  exact (by decide : 6 ≤ #({0, 1, 2, 6, 7, 8} : Finset (Fin 9))).trans (card_le_card this)

lemma pendants_G : cardPendants G = 3 := by
  unfold cardPendants
  decide +kernel

def ofBits (b : Fin 9 → Bool) : Finset (Fin 9) := univ.filter (fun i => b i)

lemma ofBits_self (D : Finset (Fin 9)) :
    ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D), decide (8 ∈ D)] = D := by
  ext i
  fin_cases i <;> simp [ofBits]

lemma indep_bits0 : ∀ b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (∀ x ∈ ofBits ![false, b1, b2, b3, b4, b5, b6, b7, b8],
      ∀ y ∈ ofBits ![false, b1, b2, b3, b4, b5, b6, b7, b8], x ≠ y → ¬ G.Adj x y) →
      #(ofBits ![false, b1, b2, b3, b4, b5, b6, b7, b8]) ≤ 4 := by
  decide +kernel

lemma indep_bits1 : ∀ b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (∀ x ∈ ofBits ![true, b1, b2, b3, b4, b5, b6, b7, b8],
      ∀ y ∈ ofBits ![true, b1, b2, b3, b4, b5, b6, b7, b8], x ≠ y → ¬ G.Adj x y) →
      #(ofBits ![true, b1, b2, b3, b4, b5, b6, b7, b8]) ≤ 4 := by
  decide +kernel

lemma indep_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (∀ x ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8],
      ∀ y ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8], x ≠ y → ¬ G.Adj x y) →
      #(ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8]) ≤ 4 := by
  intro b0
  cases b0
  · exact indep_bits0
  · exact indep_bits1

lemma indepNum_G : G.indepNum ≤ 4 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hind : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hD.isIndepSet hx hy hxy
  have := indep_bits _ _ _ _ _ _ _ _ _ ((ofBits_self D).symm ▸ hind)
  rwa [ofBits_self] at this

lemma matchingNumber_G : matchingNumber G ≤ 4 := by
  have := matchingNumber_le G
  simp only [Fintype.card_fin] at this
  omega

/-- **Graph Brain Project lower bound #47 (issue #421) is false.** -/
theorem not_conjecture47 : ¬ Conjecture47 := by
  intro h
  have h1 := h (Fin 9) G G_connected
  rw [pendants_G] at h1
  have h2 : (6 : ℝ) ≤ cardCutVertices G := by exact_mod_cast six_le_cut
  have h3 : (matchingNumber G : ℝ) ≤ 4 := by exact_mod_cast matchingNumber_G
  have h4 : (G.indepNum : ℝ) ≤ 4 := by exact_mod_cast indepNum_G
  push_cast at h1
  linarith

end GBP421_047

#print axioms GBP421_047.not_conjecture47
