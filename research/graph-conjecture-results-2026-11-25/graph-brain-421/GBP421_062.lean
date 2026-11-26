import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #62 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 62nd of the 89 lower bounds
in the issue body:

> For connected graphs:
> `independence_number(x) >= card_periphery(x)/min_degree(x) - order_automorphism_group(x)`

Counterexample: graph6 `G?qnV{` (8 vertices, 16 edges: 0-4, 0-5, 0-6, 0-7, 1-4, 1-6, 1-7, 2-5,
2-6, 2-7, 3-7, 4-5, 4-6, 4-7, 5-7, 6-7). It is asymmetric (degree + neighbour-degree colour
refinement is discrete), so its automorphism group has order 1. Vertex 7 is universal, so the
diameter is 2 and the periphery is `{0,…,6}`; the minimum degree is 1 (vertex 3); it has 12
triangles; and `α = 4`. Right-hand side `≥ 7/1 − 1 = 6 > 4`.
-/

namespace GBP421_062

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Order of the automorphism group (Sage `automorphism_group(order=True)`). -/
noncomputable def orderAut (G : SimpleGraph V) : ℕ := Nat.card (G ≃g G)

/-- An automorphism preserves the number of neighbours satisfying an invariant predicate. -/
lemma card_nbr_filter_iso (G : SimpleGraph V) [DecidableRel G.Adj] (φ : G ≃g G) (P : V → Prop)
    [DecidablePred P] (hP : ∀ w, P (φ w) ↔ P w) (v : V) :
    #((G.neighborFinset (φ v)).filter P) = #((G.neighborFinset v).filter P) := by
  symm
  apply Finset.card_bij (fun w _ => φ w)
  · intro w hw
    simp only [mem_filter, mem_neighborFinset] at hw ⊢
    exact ⟨φ.map_adj_iff.mpr hw.1, (hP w).mpr hw.2⟩
  · intro a _ b _ h
    exact φ.injective h
  · intro y hy
    simp only [mem_filter, mem_neighborFinset] at hy
    refine ⟨φ.symm y, ?_, by simp⟩
    simp only [mem_filter, mem_neighborFinset]
    have h1 : G.Adj (φ v) (φ (φ.symm y)) := by simpa using hy.1
    have h2 : P (φ (φ.symm y)) := by simpa using hy.2
    exact ⟨φ.map_adj_iff.mp h1, (hP _).mp h2⟩

lemma edist_le_two (G : SimpleGraph V) {u v : V}
    (h : u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) : G.edist u v ≤ 2 := by
  rcases h with rfl | h | ⟨w, h1, h2⟩
  · simp
  · rw [edist_eq_one_iff_adj.mpr h]; norm_num
  · exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

lemma two_le_edist (G : SimpleGraph V) (hc : G.Connected) {u v : V} (h0 : u ≠ v)
    (h1 : ¬ G.Adj u v) : 2 ≤ G.edist u v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_edist u v
  rw [← hp]
  cases p with
  | nil => exact absurd rfl h0
  | cons h p =>
    cases p with
    | nil => exact absurd h h1
    | cons _ q => simp only [Walk.length_cons]; exact_mod_cast (by omega)

open Classical in
/-- The periphery: vertices of maximum eccentricity. -/
noncomputable def periphery (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∀ u, G.eccent u ≤ G.eccent v

/-- GBP #421 lower bound #62. -/
def Conjecture62 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      (#(periphery G) : ℝ) / (G.minDegree : ℝ) - (orderAut G : ℝ) ≤ G.indepNum

/-! ### The counterexample -/

def edges : List (Fin 8 × Fin 8) :=
  [(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 6), (1, 7), (2, 5), (2, 6), (2, 7), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7), (6, 7)]

def G : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 8, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r0 : G.Reachable 7 0 := (Reachable.refl 7).trans (a 7 0 (by decide))
  have r1 : G.Reachable 7 1 := (Reachable.refl 7).trans (a 7 1 (by decide))
  have r2 : G.Reachable 7 2 := (Reachable.refl 7).trans (a 7 2 (by decide))
  have r3 : G.Reachable 7 3 := (Reachable.refl 7).trans (a 7 3 (by decide))
  have r4 : G.Reachable 7 4 := (Reachable.refl 7).trans (a 7 4 (by decide))
  have r5 : G.Reachable 7 5 := (Reachable.refl 7).trans (a 7 5 (by decide))
  have r6 : G.Reachable 7 6 := (Reachable.refl 7).trans (a 7 6 (by decide))
  have h : ∀ v : Fin 8, G.Reachable 7 v := by
    intro v
    fin_cases v
    · exact r0
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact Reachable.refl _
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

/-- Colour refinement (degree, then number of neighbours of each degree) is discrete. -/
lemma rigid_cert : ∀ u v : Fin 8, G.degree u = G.degree v →
    (∀ d : Fin 8, #((G.neighborFinset u).filter (fun w => G.degree w = d)) =
      #((G.neighborFinset v).filter (fun w => G.degree w = d))) → u = v := by
  decide +kernel

lemma iso_eq_self (φ : G ≃g G) (v : Fin 8) : φ v = v :=
  rigid_cert (φ v) v (Iso.degree_eq φ v) (fun d =>
    card_nbr_filter_iso G φ (fun w => G.degree w = d) (fun w => by rw [Iso.degree_eq]) v)

lemma orderAut_G : orderAut G = 1 := by
  haveI : Subsingleton (G ≃g G) :=
    ⟨fun a b => RelIso.ext fun v => (iso_eq_self a v).trans (iso_eq_self b v).symm⟩
  haveI : Nonempty (G ≃g G) := ⟨Iso.refl⟩
  exact Nat.card_unique

/-- Vertex 7 is universal, so any two vertices are within distance two. -/
lemma within_two : ∀ u v : Fin 8, u = v ∨ G.Adj u v ∨ ∃ x, G.Adj u x ∧ G.Adj x v := by
  decide +kernel

lemma eccent_le_two (u : Fin 8) : G.eccent u ≤ 2 :=
  (eccent_le_iff _ _).2 fun v => edist_le_two G (within_two u v)

lemma nonuniversal : ∀ v : Fin 8, v ≠ 7 → ∃ w, v ≠ w ∧ ¬ G.Adj v w := by
  decide +kernel

lemma two_le_eccent (v : Fin 8) (hv : v ≠ 7) : 2 ≤ G.eccent v := by
  obtain ⟨w, h0, h1⟩ := nonuniversal v hv
  exact (two_le_edist G G_connected h0 h1).trans edist_le_eccent

def ofBits (b : Fin 8 → Bool) : Finset (Fin 8) := univ.filter (fun i => b i)

lemma ofBits_self (D : Finset (Fin 8)) :
    ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D)] = D := by
  ext i
  fin_cases i <;> simp [ofBits]

lemma indep_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (∀ x ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7], ∀ y ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7],
      x ≠ y → ¬ G.Adj x y) → #(ofBits ![b0, b1, b2, b3, b4, b5, b6, b7]) ≤ 4 := by
  decide +kernel

lemma indepNum_G : G.indepNum ≤ 4 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hind : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hD.isIndepSet hx hy hxy
  have := indep_bits _ _ _ _ _ _ _ _ ((ofBits_self D).symm ▸ hind)
  rwa [ofBits_self] at this

lemma minDegree_G : G.minDegree = 1 :=
  le_antisymm ((minDegree_le_degree G 3).trans (by decide))
    (le_minDegree_of_forall_le_degree G 1 (by decide))

lemma seven_le_periphery : 7 ≤ #(periphery G) := by
  classical
  have : ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 8)) ⊆ periphery G := by
    intro v hv
    have hv7 : v ≠ 7 := by
      intro h; subst h; simp at hv
    simp only [periphery, mem_filter, mem_univ, true_and]
    exact fun u => (eccent_le_two u).trans (two_le_eccent v hv7)
  exact (by decide : 7 ≤ #({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 8))).trans (card_le_card this)

/-- **Graph Brain Project lower bound #62 (issue #421) is false.** -/
theorem not_conjecture62 : ¬ Conjecture62 := by
  intro h
  have h1 := h (Fin 8) G G_connected
  rw [minDegree_G, orderAut_G] at h1
  have h2 : (7 : ℝ) ≤ #(periphery G) := by exact_mod_cast seven_le_periphery
  have h3 : (G.indepNum : ℝ) ≤ 4 := by exact_mod_cast indepNum_G
  norm_num at h1
  linarith

end GBP421_062

#print axioms GBP421_062.not_conjecture62
