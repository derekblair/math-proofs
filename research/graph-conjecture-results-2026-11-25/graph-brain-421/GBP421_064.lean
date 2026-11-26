import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #64 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 64th of the 89 lower bounds in the issue body:

> For connected graphs: `independence_number(x) >= minimum(different_degrees(x), 1/cos(card_center(x)))`

`card_center` = number of vertices of minimum eccentricity; `cos` in radians.

Counterexample: graph6 `FCRdw` (7 vertices, 10 edges): degrees `[3,2,3,2,2,4,5]`, so
`different_degrees = 4`; eccentricities `[2,3,2,3,2,2,2]`, so the center has 5 vertices and
`1/cos 5 ≈ 3.525`; but `α = 3`.
-/

namespace GBP421_064

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def differentDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := #(univ.image fun v => G.degree v)

open Classical in
/-- The center: vertices of minimum eccentricity. -/
noncomputable def center (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∀ u, G.eccent v ≤ G.eccent u

/-- GBP #421 lower bound #64. -/
def Conjecture64 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      min (differentDegrees G : ℝ) (1 / Real.cos (#(center G) : ℝ)) ≤ G.indepNum

omit [Fintype V] [DecidableEq V] in
lemma edist_le_two (G : SimpleGraph V) {u v : V}
    (h : u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) : G.edist u v ≤ 2 := by
  rcases h with rfl | h | ⟨w, h1, h2⟩
  · simp
  · rw [edist_eq_one_iff_adj.mpr h]; norm_num
  · exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

omit [Fintype V] [DecidableEq V] in
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

omit [Fintype V] [DecidableEq V] in
lemma three_le_edist (G : SimpleGraph V) (hc : G.Connected) {u v : V} (h0 : u ≠ v)
    (h1 : ¬ G.Adj u v) (h2 : ∀ w, ¬ (G.Adj u w ∧ G.Adj w v)) : 3 ≤ G.edist u v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_edist u v
  rw [← hp]
  cases p with
  | nil => exact absurd rfl h0
  | cons h p =>
    cases p with
    | nil => exact absurd h h1
    | cons h' p =>
      cases p with
      | nil => exact absurd ⟨h, h'⟩ (h2 _)
      | cons _ q => simp only [Walk.length_cons]; exact_mod_cast (by omega)

/-! ### `1 / cos 5 > 3` -/

lemma cos_five_pos_and_small : 0 < Real.cos 5 ∧ Real.cos 5 < 3 / 10 := by
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  set z : ℝ := 5 - 3 * Real.pi / 2 with hz
  have hcos : Real.cos 5 = Real.sin z := by
    have : (5 : ℝ) = (z + Real.pi / 2) + Real.pi := by rw [hz]; ring
    rw [this, Real.cos_add_pi, Real.cos_add_pi_div_two]; ring
  rw [hcos]
  have hz0 : 0 < z := by rw [hz]; linarith
  have hz1 : z < 3 / 10 := by rw [hz]; linarith
  exact ⟨Real.sin_pos_of_pos_of_lt_pi hz0 (by linarith), (Real.sin_le hz0.le).trans_lt hz1⟩

lemma three_lt_inv_cos_five : 3 < 1 / Real.cos 5 := by
  obtain ⟨h0, h1⟩ := cos_five_pos_and_small
  rw [lt_div_iff₀ h0]
  linarith

/-! ### The counterexample -/

def edges : List (Fin 7 × Fin 7) :=
  [(0, 3), (0, 5), (0, 6), (1, 4), (1, 5), (2, 5), (2, 6), (3, 6), (4, 6), (5, 6)]

def G : SimpleGraph (Fin 7) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 7, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have h : ∀ v : Fin 7, G.Reachable 6 v := by
    intro v
    fin_cases v
    · exact a 6 0 (by decide)
    · exact (a 6 5 (by decide)).trans (a 5 1 (by decide))
    · exact a 6 2 (by decide)
    · exact a 6 3 (by decide)
    · exact a 6 4 (by decide)
    · exact a 6 5 (by decide)
    · exact Reachable.refl _
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

lemma differentDegrees_G : differentDegrees G = 4 := by
  unfold differentDegrees
  decide +kernel

def C : Finset (Fin 7) := {0, 2, 4, 5, 6}

lemma radius_two_cert : ∀ w ∈ C, ∀ v, w = v ∨ G.Adj w v ∨ ∃ x, G.Adj w x ∧ G.Adj x v := by
  decide +kernel

lemma nonuniversal_cert : ∀ u : Fin 7, ∃ w, u ≠ w ∧ ¬ G.Adj u w := by
  decide +kernel

lemma eccent_le_two (w : Fin 7) (hw : w ∈ C) : G.eccent w ≤ 2 :=
  (eccent_le_iff _ _).2 fun v => edist_le_two G (radius_two_cert w hw v)

lemma two_le_eccent (u : Fin 7) : 2 ≤ G.eccent u := by
  obtain ⟨w, h0, h1⟩ := nonuniversal_cert u
  exact (two_le_edist G G_connected h0 h1).trans edist_le_eccent

lemma three_le_eccent (u : Fin 7) (hu : u ∉ C) : 3 ≤ G.eccent u := by
  have : u = 1 ∨ u = 3 := by fin_cases u <;> simp_all [C]
  rcases this with rfl | rfl
  · exact (three_le_edist G G_connected (u := 1) (v := 3) (by decide) (by decide)
      (by decide)).trans edist_le_eccent
  · exact (three_le_edist G G_connected (u := 3) (v := 1) (by decide) (by decide)
      (by decide)).trans edist_le_eccent

lemma center_G : center G = C := by
  ext v
  simp only [center, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    by_contra hv
    have := (three_le_eccent v hv).trans ((h 0).trans (eccent_le_two 0 (by decide)))
    exact absurd this (by decide)
  · intro hv u
    exact (eccent_le_two v hv).trans (two_le_eccent u)

def ofBits (b : Fin 7 → Bool) : Finset (Fin 7) := univ.filter (fun i => b i)

lemma ofBits_self (D : Finset (Fin 7)) :
    ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D)] = D := by
  ext i
  fin_cases i <;> simp [ofBits]

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

/-- **Graph Brain Project lower bound #64 (issue #421) is false.** -/
theorem not_conjecture64 : ¬ Conjecture64 := by
  intro h
  have h1 := h (Fin 7) G G_connected
  rw [differentDegrees_G, center_G, show #C = 5 by decide] at h1
  have h3 : (G.indepNum : ℝ) ≤ 3 := by exact_mod_cast indepNum_G
  have h4 := three_lt_inv_cos_five
  push_cast at h1
  have : (3 : ℝ) < min 4 (1 / Real.cos 5) := lt_min (by norm_num) h4
  linarith

end GBP421_064

#print axioms GBP421_064.not_conjecture64
