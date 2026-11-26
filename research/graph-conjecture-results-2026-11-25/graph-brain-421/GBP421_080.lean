import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #80 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 80th of the 89 lower bounds:

> For connected graphs: `independence_number(x) >= -girth(x)^max_degree(x) + 2*max_even_minus_even_horizontal(x)`

`max_even_minus_even_horizontal` (gt.sage): for each vertex `v` let `E_v` be the set of vertices at
even distance from `v` (including `v`); the invariant is `max(0, max_v (|E_v| − |E(G[E_v])|))`.
For acyclic graphs Sage's girth is `+Infinity` and the bound is vacuous, so we state the
conjecture only for graphs that contain a cycle (a weaker statement, so refuting it refutes #80).

Counterexample: the Möbius ladder `M₁₃₀` (vertices `ℤ/130`, `i ~ i ± 1`, `i ~ i + 65`). It is cubic,
bipartite (parity colouring, since 65 is odd and 130 is even), connected, and contains the
4-cycle `0 − 1 − 66 − 65 − 0`, so girth 4 and max degree 3. From vertex 0 the even-distance
set is the 65 even vertices, which span no edge, so the invariant is (at least) 65. The 65 rungs
`{i, i+65}` form a perfect matching, so `α ≤ 65`. Right-hand side `≥ −4³ + 2·65 = 66 > 65 ≥ α`.
-/

namespace GBP421_080

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

/-- GBP #421 lower bound #80, for connected graphs containing a cycle (girth finite). -/
def Conjecture80 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → ¬ G.IsAcyclic →
      -((G.girth : ℝ) ^ G.maxDegree) + 2 * (meeh G : ℝ) ≤ G.indepNum

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

/-! ### The Möbius ladder `M₁₃₀` -/

/-- `i ~ i + 1` or `i ~ i + 65` (mod 130), symmetrised. -/
def R (i j : Fin 130) : Prop := (j : ℕ) = ((i : ℕ) + 1) % 130 ∨ (j : ℕ) = ((i : ℕ) + 65) % 130

instance : DecidableRel R := fun i j => by unfold R; infer_instance

def G : SimpleGraph (Fin 130) := SimpleGraph.fromRel R

instance : DecidableRel G.Adj := fun i j => by
  unfold G SimpleGraph.fromRel; simp only; infer_instance

/-- Distances from vertex 0 (BFS). -/
def d0 : Fin 130 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]

lemma cert0 : d0 0 = 0 ∧ (∀ x y, G.Adj x y → d0 y ≤ d0 x + 1) ∧
    ∀ v, v ≠ 0 → ∃ p, G.Adj v p ∧ d0 p + 1 = d0 v := by
  decide +kernel

/-- Path `i → i+1` gives every vertex a walk from 0. -/
lemma G_connected : G.Connected := by
  have hp := cert0.2.2
  have hw := walk_of_parent G 0 d0 cert0.1 hp
  refine (connected_iff_exists_forall_reachable G).2 ⟨0, fun v => ?_⟩
  obtain ⟨q, -⟩ := hw v
  exact q.reverse.reachable

lemma dist0 (v : Fin 130) : G.dist 0 v = d0 v :=
  dist_eq_of_cert G G_connected 0 d0 cert0.1 cert0.2.1 cert0.2.2 v

lemma value0 : ((#(univ.filter fun w : Fin 130 => d0 w % 2 = 0) : ℤ) -
    (edgesIn G (univ.filter fun w : Fin 130 => d0 w % 2 = 0) : ℤ)).toNat = 65 := by
  decide +kernel

lemma meeh_G : 65 ≤ meeh G := by
  unfold meeh
  have h := Finset.le_sup (f := fun v : Fin 130 =>
    ((#(evenSet G v) : ℤ) - (edgesIn G (evenSet G v) : ℤ)).toNat) (mem_univ 0)
  have e : evenSet G 0 = univ.filter fun w : Fin 130 => d0 w % 2 = 0 := by
    unfold evenSet; simp only [dist0]
  simp only [e, value0] at h
  exact h

lemma degree_le : ∀ v : Fin 130, G.degree v ≤ 3 := by decide +kernel

lemma maxDegree_G : G.maxDegree ≤ 3 := G.maxDegree_le_of_forall_degree_le 3 degree_le

lemma a01 : G.Adj 0 1 := by decide
lemma a166 : G.Adj 1 66 := by decide
lemma a6665 : G.Adj 66 65 := by decide
lemma a650 : G.Adj 65 0 := by decide

/-- The 4-cycle `0 − 1 − 66 − 65 − 0`. -/
def c4 : G.Walk 0 0 := .cons a01 (.cons a166 (.cons a6665 (.cons a650 .nil)))

lemma c4_isCycle : c4.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]; refine ⟨?_, ?_, ?_⟩ <;> decide

lemma girth_G : G.girth ≤ 4 := (girth_le_length c4_isCycle).trans (by simp [c4])

lemma not_acyclic : ¬ G.IsAcyclic := fun h => h _ c4_isCycle

/-- Distinct vertices with the same residue mod 65 are adjacent (a rung). -/
lemma rung_adj : ∀ u v : Fin 130, u ≠ v → (u : ℕ) % 65 = (v : ℕ) % 65 → G.Adj u v := by
  decide +kernel

lemma indepNum_G : G.indepNum ≤ 65 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  let f : Fin 130 → Fin 65 := fun v => ⟨(v : ℕ) % 65, Nat.mod_lt _ (by norm_num)⟩
  have hinj : Set.InjOn f D := by
    intro u hu v hv huv
    by_contra hne
    have h2 : (u : ℕ) % 65 = (v : ℕ) % 65 := congrArg Fin.val huv
    exact hD.isIndepSet hu hv hne (rung_adj u v hne h2)
  have := Finset.card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj
  simpa using this

/-- **Graph Brain Project lower bound #80 (issue #421) is false.** -/
theorem not_conjecture80 : ¬ Conjecture80 := by
  intro h
  have h1 := h (Fin 130) G G_connected not_acyclic
  have hm : (65 : ℝ) ≤ meeh G := by exact_mod_cast meeh_G
  have ha : (G.indepNum : ℝ) ≤ 65 := by exact_mod_cast indepNum_G
  have hg : (G.girth : ℝ) ≤ 4 := by exact_mod_cast girth_G
  have hd := maxDegree_G
  have hpow : (G.girth : ℝ) ^ G.maxDegree ≤ 64 := by
    have h0 : (0 : ℝ) ≤ G.girth := by positivity
    calc (G.girth : ℝ) ^ G.maxDegree ≤ 4 ^ G.maxDegree := pow_le_pow_left₀ h0 hg _
      _ ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hd
      _ = 64 := by norm_num
  linarith

end GBP421_080

#print axioms GBP421_080.not_conjecture80
