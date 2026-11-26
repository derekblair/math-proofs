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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Graph Brain Project open lower bound #45 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 45th of the 89 lower bounds:

> For connected graphs: `independence_number(x) >= tan(max_even_minus_even_horizontal(x)*order(x))/sigma_2(x)`

`max_even_minus_even_horizontal` as in gt.sage (`max(0, max_v (|E_v| − |E(G[E_v])|))`, `E_v` the
vertices at even distance from `v`); `sigma_2` (gt.sage `sigma_k(g,2)`) is the minimum degree sum of
a 2-element independent set (`+Infinity` if there is none, in which case the bound is `0` and
vacuous; we state the conjecture for graphs with a non-adjacent pair). `tan` in radians.

Counterexample: a 20-vertex tree. Spine `s₀ c₀ s₁ c₁ s₂ c₂ s₃ c₃ s₄` (vertices `0..4` = `sᵢ`,
`5..8` = `cᵢ`), with leaves `9,10,11` on `s₀` and two leaves on each other `sᵢ`. The bipartition
is `{s₀..s₄}` (5) versus the other 15 vertices; the invariant equals 15 (attained from `c₀`,
whose even-distance set is that independent 15-set), so the argument of `tan` is `15·20 = 300`.
Two leaves give `σ₂ = 2`. Each `sᵢ` together with one of its leaves forms an edge, so `V` is
covered by 15 cliques and `α ≤ 15`. But `tan 300 > 30` (`300 = 95π + π/2 − w`, `w ≈ 0.0225`), so
the right-hand side `tan 300 / 2 ≈ 22.6` exceeds `15`.
-/

namespace GBP421_045

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

/-- `sigma_2`: minimum degree sum over 2-element independent sets (for graphs having one). -/
noncomputable def sigma2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ k = G.degree u + G.degree v}

/-- GBP #421 lower bound #45, for connected graphs with a non-adjacent pair (`σ₂` finite). -/
def Conjecture45 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → (∃ u v, u ≠ v ∧ ¬ G.Adj u v) →
      Real.tan ((meeh G : ℝ) * (Fintype.card W : ℝ)) / (sigma2 G : ℝ) ≤ G.indepNum

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

/-- `tan 300 > 30`: `300 = 95π + (π/2 − w)` with `w = 191π/2 − 300 ∈ (0, 0.0229)`. -/
lemma thirty_lt_tan_300 : 30 < Real.tan 300 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hper : Real.tan 300 = Real.tan (300 - (95 : ℕ) * Real.pi) :=
    (Real.tan_periodic.sub_nat_mul_eq 95).symm
  obtain ⟨w, hw⟩ : ∃ w, w = 191 * Real.pi / 2 - 300 := ⟨_, rfl⟩
  have hz : 300 - ((95 : ℕ) : ℝ) * Real.pi = Real.pi / 2 - w := by rw [hw]; push_cast; ring
  rw [hper, hz, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hw1 : 0 < w := by rw [hw]; norm_num at hp1 ⊢; linarith
  have hw2 : w < 0.0229 := by rw [hw]; norm_num at hp2 ⊢; linarith
  have hsin0 : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw1 (by linarith)
  have hsin1 : Real.sin w ≤ w := Real.sin_le hw1.le
  have habs : |w| ≤ 1 := by rw [abs_of_pos hw1]; linarith
  have hc := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_pos hw1] at hc
  have q1 : w ^ 2 ≤ 0.0229 ^ 2 := pow_le_pow_left₀ hw1.le hw2.le 2
  have q2 : w ^ 4 ≤ 0.0229 ^ 4 := pow_le_pow_left₀ hw1.le hw2.le 4
  have hcos : 0.99 ≤ Real.cos w := by norm_num at q1 q2 ⊢; nlinarith [hc.1]
  rw [lt_div_iff₀ hsin0]
  nlinarith

/-! ### The tree -/

def R (i j : Fin 20) : Prop := (i = 5 ∧ j = 0) ∨ (i = 5 ∧ j = 1) ∨ (i = 6 ∧ j = 1) ∨ (i = 6 ∧ j = 2) ∨ (i = 7 ∧ j = 2) ∨ (i = 7 ∧ j = 3) ∨ (i = 8 ∧ j = 3) ∨ (i = 8 ∧ j = 4) ∨ (i = 0 ∧ j = 9) ∨ (i = 0 ∧ j = 10) ∨ (i = 0 ∧ j = 11) ∨ (i = 1 ∧ j = 12) ∨ (i = 1 ∧ j = 13) ∨ (i = 2 ∧ j = 14) ∨ (i = 2 ∧ j = 15) ∨ (i = 3 ∧ j = 16) ∨ (i = 3 ∧ j = 17) ∨ (i = 4 ∧ j = 18) ∨ (i = 4 ∧ j = 19)

instance : DecidableRel R := fun i j => by unfold R; infer_instance

def G : SimpleGraph (Fin 20) := SimpleGraph.fromRel R

instance : DecidableRel G.Adj := fun i j => by
  unfold G SimpleGraph.fromRel; simp only; infer_instance

/-- All-pairs distances (BFS). -/
def distT : Fin 20 → Fin 20 → ℕ := ![![0, 2, 4, 6, 8, 1, 3, 5, 7, 1, 1, 1, 3, 3, 5, 5, 7, 7, 9, 9], ![2, 0, 2, 4, 6, 1, 1, 3, 5, 3, 3, 3, 1, 1, 3, 3, 5, 5, 7, 7], ![4, 2, 0, 2, 4, 3, 1, 1, 3, 5, 5, 5, 3, 3, 1, 1, 3, 3, 5, 5], ![6, 4, 2, 0, 2, 5, 3, 1, 1, 7, 7, 7, 5, 5, 3, 3, 1, 1, 3, 3], ![8, 6, 4, 2, 0, 7, 5, 3, 1, 9, 9, 9, 7, 7, 5, 5, 3, 3, 1, 1], ![1, 1, 3, 5, 7, 0, 2, 4, 6, 2, 2, 2, 2, 2, 4, 4, 6, 6, 8, 8], ![3, 1, 1, 3, 5, 2, 0, 2, 4, 4, 4, 4, 2, 2, 2, 2, 4, 4, 6, 6], ![5, 3, 1, 1, 3, 4, 2, 0, 2, 6, 6, 6, 4, 4, 2, 2, 2, 2, 4, 4], ![7, 5, 3, 1, 1, 6, 4, 2, 0, 8, 8, 8, 6, 6, 4, 4, 2, 2, 2, 2], ![1, 3, 5, 7, 9, 2, 4, 6, 8, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10], ![1, 3, 5, 7, 9, 2, 4, 6, 8, 2, 0, 2, 4, 4, 6, 6, 8, 8, 10, 10], ![1, 3, 5, 7, 9, 2, 4, 6, 8, 2, 2, 0, 4, 4, 6, 6, 8, 8, 10, 10], ![3, 1, 3, 5, 7, 2, 2, 4, 6, 4, 4, 4, 0, 2, 4, 4, 6, 6, 8, 8], ![3, 1, 3, 5, 7, 2, 2, 4, 6, 4, 4, 4, 2, 0, 4, 4, 6, 6, 8, 8], ![5, 3, 1, 3, 5, 4, 2, 2, 4, 6, 6, 6, 4, 4, 0, 2, 4, 4, 6, 6], ![5, 3, 1, 3, 5, 4, 2, 2, 4, 6, 6, 6, 4, 4, 2, 0, 4, 4, 6, 6], ![7, 5, 3, 1, 3, 6, 4, 2, 2, 8, 8, 8, 6, 6, 4, 4, 0, 2, 4, 4], ![7, 5, 3, 1, 3, 6, 4, 2, 2, 8, 8, 8, 6, 6, 4, 4, 2, 0, 4, 4], ![9, 7, 5, 3, 1, 8, 6, 4, 2, 10, 10, 10, 8, 8, 6, 6, 4, 4, 0, 2], ![9, 7, 5, 3, 1, 8, 6, 4, 2, 10, 10, 10, 8, 8, 6, 6, 4, 4, 2, 0]]

lemma dist_cert : ∀ u : Fin 20, distT u u = 0 ∧ (∀ x y, G.Adj x y → distT u y ≤ distT u x + 1) ∧
    ∀ v, v ≠ u → ∃ p, G.Adj v p ∧ distT u p + 1 = distT u v := by
  decide +kernel

lemma G_connected : G.Connected := by
  have hw := walk_of_parent G 5 (distT 5) (dist_cert 5).1 (dist_cert 5).2.2
  refine (connected_iff_exists_forall_reachable G).2 ⟨5, fun v => ?_⟩
  obtain ⟨q, -⟩ := hw v
  exact q.reverse.reachable

lemma dist_G (u v : Fin 20) : G.dist u v = distT u v :=
  dist_eq_of_cert G G_connected u (distT u) (dist_cert u).1 (dist_cert u).2.1 (dist_cert u).2.2 v

lemma meeh_comp : (univ.sup fun v : Fin 20 =>
    ((#(univ.filter fun w => distT v w % 2 = 0) : ℤ) -
      (edgesIn G (univ.filter fun w => distT v w % 2 = 0) : ℤ)).toNat) = 15 := by
  decide +kernel

lemma meeh_G : meeh G = 15 := by
  unfold meeh evenSet
  simp only [dist_G]
  exact meeh_comp

lemma deg_pos : ∀ v : Fin 20, 1 ≤ G.degree v := by decide +kernel
lemma leaves : (9 : Fin 20) ≠ 10 ∧ ¬ G.Adj 9 10 ∧ G.degree 9 = 1 ∧ G.degree 10 = 1 := by decide +kernel

lemma sigma2_G : sigma2 G = 2 := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨9, 10, leaves.1, leaves.2.1, by rw [leaves.2.2.1, leaves.2.2.2]⟩
  · have hne : ({k | ∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ k = G.degree u + G.degree v} : Set ℕ).Nonempty :=
      ⟨2, 9, 10, leaves.1, leaves.2.1, by rw [leaves.2.2.1, leaves.2.2.2]⟩
    unfold sigma2
    apply le_csInf hne
    rintro k ⟨u, v, -, -, rfl⟩
    have := deg_pos u; have := deg_pos v; omega

/-- Clique cover by 15 parts: each `sᵢ` with one of its leaves, the rest singletons. -/
def part : Fin 20 → Fin 15 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 1, 11, 2, 12, 3, 13, 4, 14]

lemma part_adj : ∀ u v : Fin 20, u ≠ v → part u = part v → G.Adj u v := by decide +kernel

lemma indepNum_G : G.indepNum ≤ 15 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hinj : Set.InjOn part D := by
    intro u hu v hv huv
    by_contra hne
    exact hD.isIndepSet hu hv hne (part_adj u v hne huv)
  have := Finset.card_le_card_of_injOn part (fun _ _ => mem_univ _) hinj
  simpa using this

/-- **Graph Brain Project lower bound #45 (issue #421) is false.** -/
theorem not_conjecture45 : ¬ Conjecture45 := by
  intro h
  have h1 := h (Fin 20) G G_connected ⟨9, 10, leaves.1, leaves.2.1⟩
  rw [sigma2_G, Fintype.card_fin, meeh_G] at h1
  have ha : (G.indepNum : ℝ) ≤ 15 := by exact_mod_cast indepNum_G
  have e : ((15 : ℕ) : ℝ) * ((20 : ℕ) : ℝ) = 300 := by norm_num
  rw [e] at h1
  have h3 := thirty_lt_tan_300
  have h4 : (15 : ℝ) < Real.tan 300 / ((2 : ℕ) : ℝ) := by
    rw [lt_div_iff₀ (by norm_num)]; norm_num; linarith
  linarith

end GBP421_045

#print axioms GBP421_045.not_conjecture45
