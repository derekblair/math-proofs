import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #84 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 84th of the 89 lower bounds
in the issue body:

> For connected graphs: `independence_number(x) >= tan(max_even_minus_even_horizontal(x)*radius(x) + 1)`

`max_even_minus_even_horizontal` (gt.sage): for each vertex `v` let `E_v` be the set of vertices at
even distance from `v` (including `v`); the invariant is `max(0, max_v (|E_v| − |E(G[E_v])|))`.
`tan` in radians.

Counterexample (38 vertices): blow up the 14-cycle `C₁₄`, replacing bags `0, 2, 4, 6` by `K₂`
and the other ten bags by `K₃` (vertices in the same or cyclically consecutive bags are adjacent).
Every vertex has eccentricity 7, so the radius is 7; the invariant equals 5 (attained in bags
8, 10, 12: the even-distance set is `v` plus four `K₂`-bags and two `K₃`-bags); and `α = 7`
(at most one vertex from each pair of bags `{2j, 2j+1}`). Right-hand side `tan(5·7 + 1) =
tan 36 ≈ 7.7505 > 7`.
-/

namespace GBP421_084

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges of `G[S]`. -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  #((S ×ˢ S).filter fun p => G.Adj p.1 p.2) / 2

/-- Vertices at even distance from `v` (including `v`). -/
noncomputable def evenSet (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter fun w => G.dist v w % 2 = 0

/-- `max_even_minus_even_horizontal` for a connected graph. -/
noncomputable def meeh (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  univ.sup fun v => ((#(evenSet G v) : ℤ) - (edgesIn G (evenSet G v) : ℤ)).toNat

/-- GBP #421 lower bound #84. -/
def Conjecture84 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      Real.tan ((meeh G : ℝ) * (G.radius.toNat : ℝ) + 1) ≤ G.indepNum

/-- `tan 36 > 7`: `36 = 11π + (π/2 − w)` with `w = 23π/2 − 36 ∈ (0, 0.1284)`. -/
lemma seven_lt_tan_36 : 7 < Real.tan 36 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hper : Real.tan 36 = Real.tan (36 - (11 : ℕ) * Real.pi) :=
    (Real.tan_periodic.sub_nat_mul_eq 11).symm
  obtain ⟨w, hw⟩ : ∃ w, w = 23 * Real.pi / 2 - 36 := ⟨_, rfl⟩
  have hz : 36 - ((11 : ℕ) : ℝ) * Real.pi = Real.pi / 2 - w := by rw [hw]; push_cast; ring
  rw [hper, hz, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hw1 : 0 < w := by rw [hw]; norm_num at hp1 ⊢; linarith
  have hw2 : w < 0.1284 := by rw [hw]; norm_num at hp2 ⊢; linarith
  have hsin0 : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw1 (by linarith)
  have hsin1 : Real.sin w ≤ w := Real.sin_le hw1.le
  have habs : |w| ≤ 1 := by rw [abs_of_pos hw1]; linarith
  have hc := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_pos hw1] at hc
  have q1 : w ^ 2 ≤ 0.1284 ^ 2 := pow_le_pow_left₀ hw1.le hw2.le 2
  have q2 : w ^ 4 ≤ 0.1284 ^ 4 := pow_le_pow_left₀ hw1.le hw2.le 4
  have hcos : 0.99 ≤ Real.cos w := by norm_num at q1 q2 ⊢; nlinarith [hc.1]
  rw [lt_div_iff₀ hsin0]
  nlinarith

/-! ### Exact distances from a certificate -/

omit [Fintype V] [DecidableEq V] in
lemma le_walk_length (G : SimpleGraph V) (f : V → ℕ) (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) :
    ∀ {a b : V} (p : G.Walk a b), f b ≤ f a + p.length := by
  intro a b p
  induction p with
  | nil => simp
  | cons h p ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    omega

omit [Fintype V] [DecidableEq V] in
lemma walk_of_parent (G : SimpleGraph V) (u : V) (f : V → ℕ) (hu : f u = 0)
    (hp : ∀ v, v ≠ u → ∃ p, G.Adj v p ∧ f p + 1 = f v) :
    ∀ v, ∃ q : G.Walk v u, q.length = f v := by
  suffices H : ∀ m, ∀ v, f v = m → ∃ q : G.Walk v u, q.length = f v from fun v => H _ v rfl
  intro m
  induction m with
  | zero =>
    intro v hv
    by_cases h : v = u
    · subst h; exact ⟨Walk.nil, by simp [hu]⟩
    · obtain ⟨p, -, hp'⟩ := hp v h; omega
  | succ m ih =>
    intro v hv
    by_cases h : v = u
    · subst h; omega
    · obtain ⟨p, hadj, hp'⟩ := hp v h
      obtain ⟨q, hq⟩ := ih p (by omega)
      exact ⟨Walk.cons hadj q, by simp [Walk.length_cons, hq]; omega⟩

omit [Fintype V] [DecidableEq V] in
lemma dist_eq_of_cert (G : SimpleGraph V) (hc : G.Connected) (u : V) (f : V → ℕ) (hu : f u = 0)
    (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (hp : ∀ v, v ≠ u → ∃ p, G.Adj v p ∧ f p + 1 = f v) (v : V) : G.dist u v = f v := by
  apply le_antisymm
  · obtain ⟨q, hq⟩ := walk_of_parent G u f hu hp v
    rw [dist_comm, ← hq]
    exact dist_le q
  · obtain ⟨p, hp'⟩ := hc.exists_walk_length_eq_dist u v
    have := le_walk_length G f hf p
    omega

/-! ### The counterexample -/

/-- Bag (cycle position) of each vertex. -/
def bag : Fin 38 → Fin 14 := ![0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13]

/-- Same or cyclically consecutive bags. -/
def near (i j : Fin 14) : Prop := (i : ℕ) = j ∨ ((i : ℕ) + 1) % 14 = j ∨ ((j : ℕ) + 1) % 14 = i

instance : DecidableRel near := fun i j => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def G : SimpleGraph (Fin 38) := SimpleGraph.fromRel (fun a b => near (bag a) (bag b))

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (near (bag a) (bag b) ∨ near (bag b) (bag a))))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 38, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r1 : G.Reachable 0 1 := (Reachable.refl 0).trans (a 0 1 (by decide))
  have r2 : G.Reachable 0 2 := (Reachable.refl 0).trans (a 0 2 (by decide))
  have r3 : G.Reachable 0 3 := (Reachable.refl 0).trans (a 0 3 (by decide))
  have r4 : G.Reachable 0 4 := (Reachable.refl 0).trans (a 0 4 (by decide))
  have r35 : G.Reachable 0 35 := (Reachable.refl 0).trans (a 0 35 (by decide))
  have r36 : G.Reachable 0 36 := (Reachable.refl 0).trans (a 0 36 (by decide))
  have r37 : G.Reachable 0 37 := (Reachable.refl 0).trans (a 0 37 (by decide))
  have r5 : G.Reachable 0 5 := r2.trans (a 2 5 (by decide))
  have r6 : G.Reachable 0 6 := r2.trans (a 2 6 (by decide))
  have r32 : G.Reachable 0 32 := r35.trans (a 35 32 (by decide))
  have r33 : G.Reachable 0 33 := r35.trans (a 35 33 (by decide))
  have r34 : G.Reachable 0 34 := r35.trans (a 35 34 (by decide))
  have r7 : G.Reachable 0 7 := r5.trans (a 5 7 (by decide))
  have r8 : G.Reachable 0 8 := r5.trans (a 5 8 (by decide))
  have r9 : G.Reachable 0 9 := r5.trans (a 5 9 (by decide))
  have r29 : G.Reachable 0 29 := r32.trans (a 32 29 (by decide))
  have r30 : G.Reachable 0 30 := r32.trans (a 32 30 (by decide))
  have r31 : G.Reachable 0 31 := r32.trans (a 32 31 (by decide))
  have r10 : G.Reachable 0 10 := r7.trans (a 7 10 (by decide))
  have r11 : G.Reachable 0 11 := r7.trans (a 7 11 (by decide))
  have r26 : G.Reachable 0 26 := r29.trans (a 29 26 (by decide))
  have r27 : G.Reachable 0 27 := r29.trans (a 29 27 (by decide))
  have r28 : G.Reachable 0 28 := r29.trans (a 29 28 (by decide))
  have r12 : G.Reachable 0 12 := r10.trans (a 10 12 (by decide))
  have r13 : G.Reachable 0 13 := r10.trans (a 10 13 (by decide))
  have r14 : G.Reachable 0 14 := r10.trans (a 10 14 (by decide))
  have r23 : G.Reachable 0 23 := r26.trans (a 26 23 (by decide))
  have r24 : G.Reachable 0 24 := r26.trans (a 26 24 (by decide))
  have r25 : G.Reachable 0 25 := r26.trans (a 26 25 (by decide))
  have r15 : G.Reachable 0 15 := r12.trans (a 12 15 (by decide))
  have r16 : G.Reachable 0 16 := r12.trans (a 12 16 (by decide))
  have r20 : G.Reachable 0 20 := r23.trans (a 23 20 (by decide))
  have r21 : G.Reachable 0 21 := r23.trans (a 23 21 (by decide))
  have r22 : G.Reachable 0 22 := r23.trans (a 23 22 (by decide))
  have r17 : G.Reachable 0 17 := r15.trans (a 15 17 (by decide))
  have r18 : G.Reachable 0 18 := r15.trans (a 15 18 (by decide))
  have r19 : G.Reachable 0 19 := r15.trans (a 15 19 (by decide))
  have h : ∀ v : Fin 38, G.Reachable 0 v := by
    intro v
    fin_cases v
    · exact Reachable.refl _
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    · exact r7
    · exact r8
    · exact r9
    · exact r10
    · exact r11
    · exact r12
    · exact r13
    · exact r14
    · exact r15
    · exact r16
    · exact r17
    · exact r18
    · exact r19
    · exact r20
    · exact r21
    · exact r22
    · exact r23
    · exact r24
    · exact r25
    · exact r26
    · exact r27
    · exact r28
    · exact r29
    · exact r30
    · exact r31
    · exact r32
    · exact r33
    · exact r34
    · exact r35
    · exact r36
    · exact r37
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

def distT : Fin 38 → Fin 38 → ℕ := ![![0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1], ![1, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1], ![1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2], ![1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2], ![1, 1, 1, 1, 0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2], ![2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3], ![2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3], ![3, 3, 2, 2, 2, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4], ![3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4], ![3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4], ![4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5], ![4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6, 5, 5, 5], ![5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6], ![5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6], ![5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 6, 6, 6], ![6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7], ![6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7], ![7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6], ![7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6], ![7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6], ![6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5], ![6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5], ![6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5], ![5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4], ![5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4], ![5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4], ![4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3], ![4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3], ![4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3], ![3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2], ![3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1, 2, 2, 2], ![3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 2, 2, 2], ![2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1, 1, 1, 1], ![2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1, 1, 1, 1], ![2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1], ![1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 0, 1, 1], ![1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 0, 1], ![1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6, 6, 7, 7, 6, 6, 6, 5, 5, 5, 4, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 1, 1, 1, 0]]

lemma dist_cert : ∀ u : Fin 38, distT u u = 0 ∧ (∀ x y, G.Adj x y → distT u y ≤ distT u x + 1) ∧
    ∀ v, v ≠ u → ∃ p, G.Adj v p ∧ distT u p + 1 = distT u v := by
  decide +kernel

lemma dist_G (u v : Fin 38) : G.dist u v = distT u v :=
  dist_eq_of_cert G G_connected u (distT u) (dist_cert u).1 (dist_cert u).2.1 (dist_cert u).2.2 v

lemma meeh_comp : (univ.sup fun v : Fin 38 =>
    ((#(univ.filter fun w => distT v w % 2 = 0) : ℤ) -
      (edgesIn G (univ.filter fun w => distT v w % 2 = 0) : ℤ)).toNat) = 5 := by
  decide +kernel

lemma meeh_G : meeh G = 5 := by
  unfold meeh evenSet
  simp only [dist_G]
  exact meeh_comp

lemma ecc_cert : ∀ u v : Fin 38, distT u v ≤ 7 := by decide +kernel

lemma ecc_wit : ∀ u : Fin 38, ∃ v, distT u v = 7 := by decide +kernel

lemma eccent_G (u : Fin 38) : G.eccent u = 7 := by
  apply le_antisymm
  · rw [eccent_le_iff]
    intro v
    rw [← (G_connected u v).coe_dist_eq_edist, dist_G]
    exact_mod_cast ecc_cert u v
  · obtain ⟨v, hv⟩ := ecc_wit u
    have : G.edist u v = 7 := by
      rw [← (G_connected u v).coe_dist_eq_edist, dist_G, hv]; rfl
    exact this ▸ edist_le_eccent

lemma radius_G : G.radius = 7 :=
  le_antisymm ((radius_le_eccent (u := 0)).trans (eccent_G 0).le)
    (le_iInf fun u => (eccent_G u).ge)

/-- Two distinct vertices whose bags lie in the same pair `{2j, 2j+1}` are adjacent. -/
lemma pair_adj : ∀ u v : Fin 38, u ≠ v → (bag u : ℕ) / 2 = (bag v : ℕ) / 2 → G.Adj u v := by
  decide +kernel

lemma indepNum_G : G.indepNum ≤ 7 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  let f : Fin 38 → Fin 7 := fun v => ⟨(bag v : ℕ) / 2, by omega⟩
  have hinj : Set.InjOn f D := by
    intro u hu v hv huv
    by_contra hne
    have h2 : (bag u : ℕ) / 2 = (bag v : ℕ) / 2 := congrArg Fin.val huv
    exact hD.isIndepSet hu hv hne (pair_adj u v hne h2)
  have := Finset.card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj
  simpa using this

/-- **Graph Brain Project lower bound #84 (issue #421) is false.** -/
theorem not_conjecture84 : ¬ Conjecture84 := by
  intro h
  have h1 := h (Fin 38) G G_connected
  rw [meeh_G, radius_G] at h1
  have h2 : (G.indepNum : ℝ) ≤ 7 := by exact_mod_cast indepNum_G
  have h3 := seven_lt_tan_36
  have e : ((5 : ℕ) : ℝ) * ((7 : ℕ∞).toNat : ℝ) + 1 = 36 := by norm_num
  rw [e] at h1
  linarith

end GBP421_084

#print axioms GBP421_084.not_conjecture84
