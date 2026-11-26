import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# WOWII Conjecture 382c is false

Written on the Wall II (Graffiti.pc, E. DeLaViña), Conjecture 382c (Jan. 2010, status `O`):

> If G is a connected graph on n > 2 vertices, then γ₂(G) ≤ [α(G)·ecc_avg(A) + |B|]/2,
> where A is the set of minimum degree vertices and B is the set of periphery vertices.

(`γ₂` 2-domination number, def 90; `α` independence number, def 5; `ecc_avg(S)` the average
eccentricity of the vertices of `S`, def 108; periphery = vertices of maximum eccentricity, def 55.)

Counterexample: graph6 `L\DAMUobAkuFXe` (13 vertices, 35 edges). Vertex 4 is the unique vertex of
minimum degree 3 and has eccentricity 2; the periphery is `{5, 6, 8}` (eccentricity 3, all other
vertices have eccentricity 2); `α = 3`; but `γ₂ = 5 > (3·2 + 3)/2 = 4.5`. This also refutes the
special case stated in the source's comment ("if the minimum degree vertices have eccentricity
two, then γ₂ ≤ α + |B|/2").
-/

namespace WOWII382c

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `D` is 2-dominating: every vertex outside `D` has at least two neighbours in `D`. -/
def IsTwoDominating (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ #(D.filter (G.Adj v))

/-- The 2-domination number `γ₂(G)`. -/
noncomputable def twoDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ D : Finset V, IsTwoDominating G D ∧ #D = k}

/-- The set of vertices of minimum degree. -/
def minDegSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ u, G.degree v ≤ G.degree u

open Classical in
/-- The periphery: vertices of maximum eccentricity. -/
noncomputable def periphery (G : SimpleGraph V) : Finset V :=
  univ.filter fun v => ∀ u, G.eccent u ≤ G.eccent v

/-- Average eccentricity of the vertices of `S`. -/
noncomputable def eccAvg (G : SimpleGraph V) (S : Finset V) : ℝ :=
  (∑ v ∈ S, ((G.eccent v).toNat : ℝ)) / #S

/-- WOWII Conjecture 382c. -/
def Conjecture382c : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card W →
      (twoDominationNumber G : ℝ) ≤ (G.indepNum * eccAvg G (minDegSet G) + #(periphery G)) / 2

/-! ### General lemmas -/

omit [DecidableEq V] in
lemma le_twoDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ D : Finset V, IsTwoDominating G D → k ≤ #D) : k ≤ twoDominationNumber G := by
  apply le_csInf
  · exact ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  · rintro m ⟨D, hD, rfl⟩
    exact h D hD

omit [Fintype V] [DecidableEq V] in
lemma edist_le_two (G : SimpleGraph V) {u v : V}
    (h : u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) : G.edist u v ≤ 2 := by
  rcases h with rfl | h | ⟨w, h1, h2⟩
  · simp
  · rw [edist_eq_one_iff_adj.mpr h]; norm_num
  · exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

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

/-! ### The counterexample -/

/-- Edge list of the graph with graph6 code `L\DAMUobAkuFXe`. -/
def edges : List (Fin 13 × Fin 13) :=
  [(0, 2), (0, 3), (0, 7), (0, 8), (0, 9), (0, 11), (1, 2), (1, 5), (1, 6), (1, 7), (1, 10), (1, 12),
   (2, 3), (2, 8), (2, 11), (2, 12), (3, 4), (3, 8), (3, 10), (3, 11), (4, 7), (4, 9), (5, 6), (5, 9),
   (5, 10), (5, 12), (6, 7), (6, 10), (6, 12), (8, 11), (9, 10), (9, 11), (9, 12), (10, 11), (10, 12)]

def G : SimpleGraph (Fin 13) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 13, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have h : ∀ v : Fin 13, G.Reachable 0 v := by
    have r2 : G.Reachable 0 2 := a 0 2 (by decide)
    have r3 : G.Reachable 0 3 := a 0 3 (by decide)
    have r7 : G.Reachable 0 7 := a 0 7 (by decide)
    have r9 : G.Reachable 0 9 := a 0 9 (by decide)
    intro v
    fin_cases v
    · exact Reachable.refl _
    · exact r2.trans (a 2 1 (by decide))
    · exact r2
    · exact r3
    · exact r3.trans (a 3 4 (by decide))
    · exact r9.trans (a 9 5 (by decide))
    · exact r7.trans (a 7 6 (by decide))
    · exact r7
    · exact a 0 8 (by decide)
    · exact r9
    · exact r3.trans (a 3 10 (by decide))
    · exact a 0 11 (by decide)
    · exact r2.trans (a 2 12 (by decide))
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

lemma minDeg_G : minDegSet G = {4} := by
  decide +kernel

/-- Every vertex outside `{5, 6, 8}` reaches every vertex within two steps. -/
lemma radius_two_cert : ∀ w : Fin 13, w ∉ ({5, 6, 8} : Finset (Fin 13)) →
    ∀ v, w = v ∨ G.Adj w v ∨ ∃ x, G.Adj w x ∧ G.Adj x v := by
  decide +kernel

lemma eccent_le_two (w : Fin 13) (hw : w ∉ ({5, 6, 8} : Finset (Fin 13))) : G.eccent w ≤ 2 :=
  (eccent_le_iff _ _).2 fun v => edist_le_two G (radius_two_cert w hw v)

lemma three_le_eccent_five : 3 ≤ G.eccent 5 :=
  (three_le_edist G G_connected (u := 5) (v := 8) (by decide) (by decide) (by decide)).trans
    edist_le_eccent

lemma periphery_G_subset : periphery G ⊆ {5, 6, 8} := by
  intro w hw
  by_contra hn
  have hw' : ∀ u, G.eccent u ≤ G.eccent w := by
    simpa [periphery] using hw
  have := three_le_eccent_five.trans ((hw' 5).trans (eccent_le_two w hn))
  exact absurd this (by decide)

lemma card_periphery_G : #(periphery G) ≤ 3 :=
  (card_le_card periphery_G_subset).trans (by decide)

lemma eccAvg_G : eccAvg G (minDegSet G) ≤ 2 := by
  rw [minDeg_G, eccAvg, sum_singleton, card_singleton, Nat.cast_one, div_one]
  have h := eccent_le_two 4 (by decide)
  have : (G.eccent 4).toNat ≤ 2 := ENat.toNat_le_of_le_natCast h
  exact_mod_cast this

/-- Vertex set from a bit vector. -/
def ofBits (b : Fin 13 → Bool) : Finset (Fin 13) := univ.filter (fun i => b i)

/-- No set of at most four vertices 2-dominates `G` (all 8192 vertex sets). -/
lemma twoDom_bits_0 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    IsTwoDominating G (ofBits ![false, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) → 5 ≤ #(ofBits ![false, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_1 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    IsTwoDominating G (ofBits ![false, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) → 5 ≤ #(ofBits ![false, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_2 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    IsTwoDominating G (ofBits ![true, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) → 5 ≤ #(ofBits ![true, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_3 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    IsTwoDominating G (ofBits ![true, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) → 5 ≤ #(ofBits ![true, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    IsTwoDominating G (ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) → 5 ≤ #(ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) := by
  intro b0 b1
  cases b0 <;> cases b1
  · exact twoDom_bits_0
  · exact twoDom_bits_1
  · exact twoDom_bits_2
  · exact twoDom_bits_3

/-- No independent set has more than three vertices (all 8192 vertex sets). -/
lemma indep_bits_0 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    (∀ x ∈ ofBits ![false, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], ∀ y ∈ ofBits ![false, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], x ≠ y → ¬ G.Adj x y) → #(ofBits ![false, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) ≤ 3 := by
  decide +kernel

lemma indep_bits_1 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    (∀ x ∈ ofBits ![false, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], ∀ y ∈ ofBits ![false, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], x ≠ y → ¬ G.Adj x y) → #(ofBits ![false, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) ≤ 3 := by
  decide +kernel

lemma indep_bits_2 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    (∀ x ∈ ofBits ![true, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], ∀ y ∈ ofBits ![true, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], x ≠ y → ¬ G.Adj x y) → #(ofBits ![true, false, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) ≤ 3 := by
  decide +kernel

lemma indep_bits_3 : ∀ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    (∀ x ∈ ofBits ![true, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], ∀ y ∈ ofBits ![true, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], x ≠ y → ¬ G.Adj x y) → #(ofBits ![true, true, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) ≤ 3 := by
  decide +kernel

lemma indep_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool,
    (∀ x ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], ∀ y ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12], x ≠ y → ¬ G.Adj x y) → #(ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]) ≤ 3 := by
  intro b0 b1
  cases b0 <;> cases b1
  · exact indep_bits_0
  · exact indep_bits_1
  · exact indep_bits_2
  · exact indep_bits_3

lemma five_le_twoDom : 5 ≤ twoDominationNumber G := by
  apply le_twoDominationNumber
  intro D hD
  have hD' : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D), decide (8 ∈ D),
      decide (9 ∈ D), decide (10 ∈ D), decide (11 ∈ D), decide (12 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits]
  have := twoDom_bits _ _ _ _ _ _ _ _ _ _ _ _ _ (hD'.symm ▸ hD)
  rwa [hD'] at this

lemma indepNum_G : G.indepNum ≤ 3 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hD' : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D), decide (8 ∈ D),
      decide (9 ∈ D), decide (10 ∈ D), decide (11 ∈ D), decide (12 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits]
  have hind : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hD.isIndepSet hx hy hxy
  have := indep_bits _ _ _ _ _ _ _ _ _ _ _ _ _ (hD'.symm ▸ hind)
  rwa [hD'] at this

/-- **WOWII Conjecture 382c is false.** -/
theorem not_conjecture382c : ¬ Conjecture382c := by
  intro h
  have h1 := h (Fin 13) G G_connected (by simp)
  have h2 : (5 : ℝ) ≤ twoDominationNumber G := by exact_mod_cast five_le_twoDom
  have h3 : (G.indepNum : ℝ) ≤ 3 := by exact_mod_cast indepNum_G
  have h4 := eccAvg_G
  have h5 : (#(periphery G) : ℝ) ≤ 3 := by exact_mod_cast card_periphery_G
  have h6 : (0 : ℝ) ≤ G.indepNum := by positivity
  have h7 : (0 : ℝ) ≤ eccAvg G (minDegSet G) := by
    unfold eccAvg
    exact div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith [mul_le_mul h3 h4 h7 (by norm_num : (0:ℝ) ≤ 3)]

end WOWII382c

#print axioms WOWII382c.not_conjecture382c
