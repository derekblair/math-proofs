import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic

/-!
# Graph Brain Project open lower bound #29 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 ("A complete list of open alpha
conjectures", 7 Sep 2017), 29th of the 89 lower bounds in the issue body:

> For connected graphs: `independence_number(x) >= 2*different_degrees(x) - 2*szekeres_wilf(x)`

`different_degrees` = number of distinct vertex degrees; `szekeres_wilf` = 1 + the maximum,
over all (induced) subgraphs, of the minimum degree (= 1 + degeneracy).

Counterexample: graph6 `FCRfg` (7 vertices, 10 edges), degrees `[1,2,2,3,3,4,5]`, so
`different_degrees = 5`; every nonempty vertex set contains a vertex with at most two
neighbours inside it, so `szekeres_wilf ≤ 3`; `α = 3`. RHS `≥ 10 - 6 = 4 > 3`.
-/

namespace GBP421_029

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of distinct vertex degrees. -/
def differentDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := #(univ.image fun v => G.degree v)

/-- Szekeres–Wilf number: `1 + max_{∅ ≠ S ⊆ V} min_{v ∈ S} deg_{G[S]} v`. -/
noncomputable def szekeresWilf (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact 1 + Nat.findGreatest
    (fun k => ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, k ≤ #(S.filter (G.Adj v))) (Fintype.card V)

/-- GBP #421 lower bound #29. -/
def Conjecture29 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      2 * (differentDegrees G : ℝ) - 2 * (szekeresWilf G : ℝ) ≤ G.indepNum

lemma szekeresWilf_le (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, #(S.filter (G.Adj v)) < k) :
    szekeresWilf G ≤ k := by
  classical
  unfold szekeresWilf
  set m := Nat.findGreatest
    (fun k => ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, k ≤ #(S.filter (G.Adj v))) (Fintype.card V)
    with hm
  by_cases h0 : m = 0
  · omega
  · obtain ⟨S, hS, hall⟩ := Nat.findGreatest_of_ne_zero hm.symm h0
    obtain ⟨v, hv, hlt⟩ := h S hS
    have := hall v hv
    omega

/-! ### The counterexample -/

def edges : List (Fin 7 × Fin 7) :=
  [(0, 3), (0, 5), (0, 6), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 6), (5, 6)]

def G : SimpleGraph (Fin 7) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 7, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have h : ∀ v : Fin 7, G.Reachable 6 v := by
    intro v
    fin_cases v
    · exact a 6 0 (by decide)
    · exact a 6 1 (by decide)
    · exact a 6 2 (by decide)
    · exact a 6 3 (by decide)
    · exact (a 6 1 (by decide)).trans (a 1 4 (by decide))
    · exact a 6 5 (by decide)
    · exact Reachable.refl _
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

lemma differentDegrees_G : differentDegrees G = 5 := by
  unfold differentDegrees
  decide +kernel

def ofBits (b : Fin 7 → Bool) : Finset (Fin 7) := univ.filter (fun i => b i)

lemma ofBits_self (D : Finset (Fin 7)) :
    ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D)] = D := by
  ext i
  fin_cases i <;> simp [ofBits]

lemma sw_bits : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (ofBits ![b0, b1, b2, b3, b4, b5, b6]).Nonempty →
      ∃ v ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6],
        #((ofBits ![b0, b1, b2, b3, b4, b5, b6]).filter (G.Adj v)) < 3 := by
  decide +kernel

lemma szekeresWilf_G : szekeresWilf G ≤ 3 := by
  apply szekeresWilf_le G 3 (by norm_num)
  intro S hS
  have := sw_bits _ _ _ _ _ _ _ ((ofBits_self S).symm ▸ hS)
  rwa [ofBits_self] at this

lemma indep_bits : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (∀ x ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6], ∀ y ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6],
      x ≠ y → ¬ G.Adj x y) → #(ofBits ![b0, b1, b2, b3, b4, b5, b6]) ≤ 3 := by
  decide +kernel

lemma indepNum_G : G.indepNum ≤ 3 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hind : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hD.isIndepSet hx hy hxy
  have := indep_bits _ _ _ _ _ _ _ ((ofBits_self D).symm ▸ hind)
  rwa [ofBits_self] at this

/-- **Graph Brain Project lower bound #29 (issue #421) is false.** -/
theorem not_conjecture29 : ¬ Conjecture29 := by
  intro h
  have h1 := h (Fin 7) G G_connected
  rw [differentDegrees_G] at h1
  have h2 : (szekeresWilf G : ℝ) ≤ 3 := by exact_mod_cast szekeresWilf_G
  have h3 : (G.indepNum : ℝ) ≤ 3 := by exact_mod_cast indepNum_G
  push_cast at h1
  linarith

end GBP421_029

#print axioms GBP421_029.not_conjecture29
