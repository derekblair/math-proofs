import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #85 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 85th of the 89 lower bounds
in the issue body:

> For connected graphs: `independence_number(x) >= arcsinh(tan(e^sin(average_distance(x))))`

`average_distance` = mean distance over pairs of distinct vertices (Sage `average_distance`,
Wiener index / C(n,2)); trigonometric functions in radians.

Counterexample: graph6 `G?B@dO`, the 8-vertex tree with edges
0-5, 0-7, 1-5, 2-6, 2-7, 3-6, 4-7. Wiener index 75, so the average distance is 75/28;
sin(75/28) ≈ 0.44665, e^that ≈ 1.56307 (just below π/2), tan ≈ 129.46, arsinh ≈ 5.5566.
But α = 5.
-/

namespace GBP421_085

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Average distance over ordered pairs of distinct vertices
(the diagonal contributes 0, so this is the Wiener index divided by `C(n,2)`). -/
noncomputable def averageDistance (G : SimpleGraph V) : ℝ :=
  (∑ u, ∑ v, (G.dist u v : ℝ)) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))

/-- GBP #421 lower bound #85. -/
def Conjecture85 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      Real.arsinh (Real.tan (Real.exp (Real.sin (averageDistance G)))) ≤ G.indepNum

/-! ### Real-analysis bounds: `arsinh (tan (exp (sin (75/28)))) > 5` -/

lemma sin_bounds : 0.444 < Real.sin (75 / 28) ∧ Real.sin (75 / 28) < 0.449 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  set y : ℝ := Real.pi - 75 / 28 with hy
  have hs : Real.sin (75 / 28) = Real.sin y := by rw [hy, Real.sin_pi_sub]
  have hy1 : 0.4629 ≤ y := by rw [hy]; norm_num at hp1 ⊢; linarith
  have hy2 : y ≤ 0.4631 := by rw [hy]; norm_num at hp2 ⊢; linarith
  have hy0 : 0 ≤ y := by linarith
  have habs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; linarith
  have hb := Real.sin_bound habs
  rw [abs_of_nonneg hy0] at hb
  have hb' := abs_le.mp hb
  have c1 : y ^ 3 ≤ 0.4631 ^ 3 := pow_le_pow_left₀ hy0 hy2 3
  have c2 : 0.4629 ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy1 3
  have c3 : y ^ 5 ≤ 0.4631 ^ 5 := pow_le_pow_left₀ hy0 hy2 5
  rw [hs]
  constructor <;> norm_num at c1 c2 c3 ⊢ <;> linarith [hb'.1, hb'.2]

lemma exp_lower : (1.5585 : ℝ) < Real.exp 0.444 := by
  have h := Real.exp_bound (x := 0.444) (by norm_num [abs_of_nonneg]) (n := 5) (by norm_num)
  have h' := abs_le.mp h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_nonneg] at h'
  norm_num
  linarith [h'.1]

lemma exp_upper : Real.exp 0.449 < (1.5668 : ℝ) := by
  have h := Real.exp_bound (x := 0.449) (by norm_num [abs_of_nonneg]) (n := 5) (by norm_num)
  have h' := abs_le.mp h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_nonneg] at h'
  norm_num
  linarith [h'.2]

lemma sinh_five_lt : Real.sinh 5 < 75 := by
  rw [Real.sinh_eq]
  have h1 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h2 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := pow_lt_pow_left₀ he he0 (by norm_num)
  have h3 := Real.exp_pos (-5)
  rw [h1]
  norm_num at h2 ⊢
  linarith

lemma tan_big (z : ℝ) (hz1 : 1.5585 < z) (hz2 : z < 1.5668) : 75 < Real.tan z := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  obtain ⟨w, rfl⟩ : ∃ w, z = Real.pi / 2 - w := ⟨Real.pi / 2 - z, by ring⟩
  have hw1 : 0 < w := by norm_num at hp1 hz2 ⊢; linarith
  have hw2 : w < 0.0124 := by norm_num at hp2 hz1 ⊢; linarith
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hsin0 : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw1 (by linarith)
  have hsin1 : Real.sin w ≤ w := Real.sin_le hw1.le
  have habs : |w| ≤ 1 := by rw [abs_of_pos hw1]; linarith
  have hc := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_pos hw1] at hc
  have q1 : w ^ 2 ≤ 0.0124 ^ 2 := pow_le_pow_left₀ hw1.le hw2.le 2
  have q2 : w ^ 4 ≤ 0.0124 ^ 4 := pow_le_pow_left₀ hw1.le hw2.le 4
  have hcos : 0.99 ≤ Real.cos w := by norm_num at q1 q2 ⊢; nlinarith [hc.1]
  rw [lt_div_iff₀ hsin0]
  nlinarith

lemma key_bound : 5 < Real.arsinh (Real.tan (Real.exp (Real.sin (75 / 28)))) := by
  obtain ⟨s1, s2⟩ := sin_bounds
  have e1 : Real.exp 0.444 < Real.exp (Real.sin (75 / 28)) := Real.exp_lt_exp.mpr s1
  have e2 : Real.exp (Real.sin (75 / 28)) < Real.exp 0.449 := Real.exp_lt_exp.mpr s2
  have ht := tan_big _ (exp_lower.trans e1) (e2.trans exp_upper)
  have : Real.sinh 5 < Real.tan (Real.exp (Real.sin (75 / 28))) := sinh_five_lt.trans ht
  have := Real.arsinh_lt_arsinh.mpr this
  rwa [Real.arsinh_sinh] at this

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

def edges : List (Fin 8 × Fin 8) :=
  [(0, 5), (0, 7), (1, 5), (2, 6), (2, 7), (3, 6), (4, 7)]

def G : SimpleGraph (Fin 8) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 8, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r0 : G.Reachable 7 0 := (Reachable.refl 7).trans (a 7 0 (by decide))
  have r2 : G.Reachable 7 2 := (Reachable.refl 7).trans (a 7 2 (by decide))
  have r4 : G.Reachable 7 4 := (Reachable.refl 7).trans (a 7 4 (by decide))
  have r5 : G.Reachable 7 5 := r0.trans (a 0 5 (by decide))
  have r6 : G.Reachable 7 6 := r2.trans (a 2 6 (by decide))
  have r1 : G.Reachable 7 1 := r5.trans (a 5 1 (by decide))
  have r3 : G.Reachable 7 3 := r6.trans (a 6 3 (by decide))
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

def distT : Fin 8 → Fin 8 → ℕ := ![![0, 2, 2, 4, 2, 1, 3, 1], ![2, 0, 4, 6, 4, 1, 5, 3], ![2, 4, 0, 2, 2, 3, 1, 1], ![4, 6, 2, 0, 4, 5, 1, 3], ![2, 4, 2, 4, 0, 3, 3, 1], ![1, 1, 3, 5, 3, 0, 4, 2], ![3, 5, 1, 1, 3, 4, 0, 2], ![1, 3, 1, 3, 1, 2, 2, 0]]

lemma dist_cert : ∀ u : Fin 8, distT u u = 0 ∧ (∀ x y, G.Adj x y → distT u y ≤ distT u x + 1) ∧
    ∀ v, v ≠ u → ∃ p, G.Adj v p ∧ distT u p + 1 = distT u v := by
  decide +kernel

lemma dist_G (u v : Fin 8) : G.dist u v = distT u v :=
  dist_eq_of_cert G G_connected u (distT u) (dist_cert u).1 (dist_cert u).2.1 (dist_cert u).2.2 v

lemma averageDistance_G : averageDistance G = 75 / 28 := by
  unfold averageDistance
  simp only [dist_G, Fintype.card_fin]
  have : (∑ u : Fin 8, ∑ v : Fin 8, distT u v) = 150 := by decide
  have h2 : (∑ u : Fin 8, ∑ v : Fin 8, (distT u v : ℝ)) = 150 := by exact_mod_cast this
  rw [h2]
  norm_num

def ofBits (b : Fin 8 → Bool) : Finset (Fin 8) := univ.filter (fun i => b i)

lemma ofBits_self (D : Finset (Fin 8)) :
    ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D)] = D := by
  ext i
  fin_cases i <;> simp [ofBits]

lemma indep_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (∀ x ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7], ∀ y ∈ ofBits ![b0, b1, b2, b3, b4, b5, b6, b7],
      x ≠ y → ¬ G.Adj x y) → #(ofBits ![b0, b1, b2, b3, b4, b5, b6, b7]) ≤ 5 := by
  decide +kernel

lemma indepNum_G : G.indepNum ≤ 5 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hind : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ¬ G.Adj x y :=
    fun x hx y hy hxy => hD.isIndepSet hx hy hxy
  have := indep_bits _ _ _ _ _ _ _ _ ((ofBits_self D).symm ▸ hind)
  rwa [ofBits_self] at this

/-- **Graph Brain Project lower bound #85 (issue #421) is false.** -/
theorem not_conjecture85 : ¬ Conjecture85 := by
  intro h
  have h1 := h (Fin 8) G G_connected
  rw [averageDistance_G] at h1
  have h2 : (G.indepNum : ℝ) ≤ 5 := by exact_mod_cast indepNum_G
  have h3 := key_bound
  linarith

end GBP421_085

#print axioms GBP421_085.not_conjecture85
