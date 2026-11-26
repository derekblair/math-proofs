import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# Graph Brain Project open lower bound #35 on the independence number is false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 35th of the 89 lower bounds
in the issue body:

> For connected graphs:
> `independence_number(x) >= ceil(tan(min_degree(x))) - order_automorphism_group(x)`

(`tan` in radians.) Counterexample: the complement `G` of an asymmetric triangle-free graph `H`
with maximum degree 3 on 18 vertices (graph6 of `G`: `Q^ju~~~^}^~b~~}v^z}vz~\~~|w`; edges of `H`:
0-1, 0-9, 1-4, 2-6, 2-10, 2-15, 3-4, 3-10, 4-5, 5-13, 5-15, 6-11, 6-16, 7-11, 8-11, 8-13, 8-14, 10-16, 12-13, 12-15, 12-17). Then `δ(G) = 17 − 3 = 14`,
`⌈tan 14⌉ = ⌈7.2446…⌉ = 8`, `|Aut G| = |Aut H| = 1` (colour refinement is discrete after 3
rounds), and `α(G) = ω(H) = 2` (we only need `α(G) ≤ 4`, from `Δ(H) ≤ 3`).
Right-hand side `= 8 − 1 = 7 > 2`.
-/

namespace GBP421_035

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Order of the automorphism group (Sage `automorphism_group(order=True)`). -/
noncomputable def orderAut (G : SimpleGraph V) : ℕ := Nat.card (G ≃g G)

/-- GBP #421 lower bound #35. -/
def Conjecture35 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      (⌈Real.tan (G.minDegree : ℝ)⌉ : ℝ) - (orderAut G : ℝ) ≤ G.indepNum

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

/-- One round of colour refinement preserves automorphism-invariance. -/
lemma refine_step (G : SimpleGraph V) [DecidableRel G.Adj] (φ : G ≃g G) {m : ℕ}
    (T T' : V → Fin m) (hT : ∀ v, T (φ v) = T v)
    (cert : ∀ u v, T u = T v → (∀ c : Fin m, #((G.neighborFinset u).filter (fun w => T w = c)) =
      #((G.neighborFinset v).filter (fun w => T w = c))) → T' u = T' v) :
    ∀ v, T' (φ v) = T' v :=
  fun v => cert (φ v) v (hT v)
    (fun c => card_nbr_filter_iso G φ (fun w => T w = c) (fun w => by rw [hT]) v)

/-- An independent set containing `v` lies in `{v} ∪` the non-neighbours of `v`. -/
lemma indep_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ v, #(univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w) ≤ k) : G.indepNum ≤ k + 1 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  rcases D.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp
  · have hsub : D.erase v ⊆ univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w := by
      intro w hw
      rw [mem_erase] at hw
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hw.1, hD.isIndepSet hv hw.2 (Ne.symm hw.1)⟩
    have := (card_le_card hsub).trans (h v)
    rw [card_erase_of_mem hv] at this
    omega

/-- `7 < tan 14 ≤ 8`, so `⌈tan 14⌉ = 8`. -/
lemma ceil_tan_fourteen : ⌈Real.tan 14⌉ = 8 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hper : Real.tan 14 = Real.tan (14 - (4 : ℕ) * Real.pi) :=
    (Real.tan_periodic.sub_nat_mul_eq 4).symm
  obtain ⟨w, hw⟩ : ∃ w, w = 9 * Real.pi / 2 - 14 := ⟨_, rfl⟩
  have hz : 14 - ((4 : ℕ) : ℝ) * Real.pi = Real.pi / 2 - w := by rw [hw]; push_cast; ring
  rw [hper, hz, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hw1 : 0.1367 < w := by rw [hw]; norm_num at hp1 ⊢; linarith
  have hw2 : w < 0.1372 := by rw [hw]; norm_num at hp2 ⊢; linarith
  have hw0 : 0 < w := by linarith
  have hsin0 : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith)
  have hsin1 : Real.sin w ≤ w := Real.sin_le hw0.le
  have hsin2 : w - w ^ 3 / 6 < Real.sin w := Real.sin_gt_sub_cube hw0
  have habs : |w| ≤ 1 := by rw [abs_of_pos hw0]; linarith
  have hc := abs_le.mp (Real.cos_bound habs)
  rw [abs_of_pos hw0] at hc
  have q1 : w ^ 2 ≤ 0.1372 ^ 2 := pow_le_pow_left₀ hw0.le hw2.le 2
  have q2 : w ^ 4 ≤ 0.1372 ^ 4 := pow_le_pow_left₀ hw0.le hw2.le 4
  have q3 : w ^ 3 ≤ 0.1372 ^ 3 := pow_le_pow_left₀ hw0.le hw2.le 3
  have hcos : 0.99 ≤ Real.cos w := by norm_num at q1 q2 ⊢; nlinarith [hc.1]
  have hcos1 : Real.cos w ≤ 1 := Real.cos_le_one w
  have hs3 : 0.136 < Real.sin w := by norm_num at q3 ⊢; nlinarith
  rw [Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ hsin0]; push_cast; nlinarith
  · rw [div_le_iff₀ hsin0]; push_cast; nlinarith

/-! ### The counterexample -/

def edges : List (Fin 18 × Fin 18) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (1, 2), (1, 3), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (2, 3), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9), (2, 11), (2, 12), (2, 13), (2, 14), (2, 16), (2, 17), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (4, 16), (4, 17), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 14), (5, 16), (5, 17), (6, 7), (6, 8), (6, 9), (6, 10), (6, 12), (6, 13), (6, 14), (6, 15), (6, 17), (7, 8), (7, 9), (7, 10), (7, 12), (7, 13), (7, 14), (7, 15), (7, 16), (7, 17), (8, 9), (8, 10), (8, 12), (8, 15), (8, 16), (8, 17), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15), (9, 16), (9, 17), (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (10, 17), (11, 12), (11, 13), (11, 14), (11, 15), (11, 16), (11, 17), (12, 14), (12, 16), (13, 14), (13, 15), (13, 16), (13, 17), (14, 15), (14, 16), (14, 17), (15, 16), (15, 17), (16, 17)]

def G : SimpleGraph (Fin 18) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 18, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r2 : G.Reachable 0 2 := (Reachable.refl 0).trans (a 0 2 (by decide))
  have r3 : G.Reachable 0 3 := (Reachable.refl 0).trans (a 0 3 (by decide))
  have r4 : G.Reachable 0 4 := (Reachable.refl 0).trans (a 0 4 (by decide))
  have r5 : G.Reachable 0 5 := (Reachable.refl 0).trans (a 0 5 (by decide))
  have r6 : G.Reachable 0 6 := (Reachable.refl 0).trans (a 0 6 (by decide))
  have r7 : G.Reachable 0 7 := (Reachable.refl 0).trans (a 0 7 (by decide))
  have r8 : G.Reachable 0 8 := (Reachable.refl 0).trans (a 0 8 (by decide))
  have r10 : G.Reachable 0 10 := (Reachable.refl 0).trans (a 0 10 (by decide))
  have r11 : G.Reachable 0 11 := (Reachable.refl 0).trans (a 0 11 (by decide))
  have r12 : G.Reachable 0 12 := (Reachable.refl 0).trans (a 0 12 (by decide))
  have r13 : G.Reachable 0 13 := (Reachable.refl 0).trans (a 0 13 (by decide))
  have r14 : G.Reachable 0 14 := (Reachable.refl 0).trans (a 0 14 (by decide))
  have r15 : G.Reachable 0 15 := (Reachable.refl 0).trans (a 0 15 (by decide))
  have r16 : G.Reachable 0 16 := (Reachable.refl 0).trans (a 0 16 (by decide))
  have r17 : G.Reachable 0 17 := (Reachable.refl 0).trans (a 0 17 (by decide))
  have r1 : G.Reachable 0 1 := r2.trans (a 2 1 (by decide))
  have r9 : G.Reachable 0 9 := r2.trans (a 2 9 (by decide))
  have h : ∀ v : Fin 18, G.Reachable 0 v := by
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
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

def T0 : Fin 18 → Fin 18 := ![1, 1, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 1, 2]

def T1 : Fin 18 → Fin 18 := ![4, 5, 3, 6, 0, 3, 2, 8, 1, 7, 0, 1, 1, 3, 8, 3, 6, 8]

def T2 : Fin 18 → Fin 18 := ![10, 11, 9, 13, 1, 8, 5, 15, 3, 14, 0, 4, 2, 7, 15, 6, 12, 15]

def T3 : Fin 18 → Fin 18 := ![10, 11, 9, 13, 1, 8, 5, 15, 3, 14, 0, 4, 2, 7, 16, 6, 12, 17]

lemma base : ∀ u v : Fin 18, G.degree u = G.degree v → T0 u = T0 v := by
  decide +kernel

lemma step0 : ∀ u v : Fin 18, T0 u = T0 v →
    (∀ c : Fin 18, #((G.neighborFinset u).filter (fun w => T0 w = c)) =
      #((G.neighborFinset v).filter (fun w => T0 w = c))) → T1 u = T1 v := by
  decide +kernel

lemma step1 : ∀ u v : Fin 18, T1 u = T1 v →
    (∀ c : Fin 18, #((G.neighborFinset u).filter (fun w => T1 w = c)) =
      #((G.neighborFinset v).filter (fun w => T1 w = c))) → T2 u = T2 v := by
  decide +kernel

lemma step2 : ∀ u v : Fin 18, T2 u = T2 v →
    (∀ c : Fin 18, #((G.neighborFinset u).filter (fun w => T2 w = c)) =
      #((G.neighborFinset v).filter (fun w => T2 w = c))) → T3 u = T3 v := by
  decide +kernel

lemma final_inj : ∀ u v : Fin 18, T3 u = T3 v → u = v := by
  decide +kernel

lemma iso_eq_self (φ : G ≃g G) (v : Fin 18) : φ v = v := by
  have h0 : ∀ v, T0 (φ v) = T0 v := fun v => base (φ v) v (Iso.degree_eq φ v)
  have h1 := refine_step G φ T0 T1 h0 step0
  have h2 := refine_step G φ T1 T2 h1 step1
  have h3 := refine_step G φ T2 T3 h2 step2
  exact final_inj _ _ (h3 v)

lemma orderAut_G : orderAut G = 1 := by
  have : Subsingleton (G ≃g G) :=
    ⟨fun a b => RelIso.ext fun v => (iso_eq_self a v).trans (iso_eq_self b v).symm⟩
  have : Nonempty (G ≃g G) := ⟨Iso.refl⟩
  exact Nat.card_unique

lemma minDegree_G : G.minDegree = 14 :=
  le_antisymm ((minDegree_le_degree G 2).trans (by decide +kernel))
    (le_minDegree_of_forall_le_degree G 14 (by decide +kernel))

lemma nonnbr_le : ∀ v : Fin 18, #(univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w) ≤ 3 := by
  decide +kernel

/-- **Graph Brain Project lower bound #35 (issue #421) is false.** -/
theorem not_conjecture35 : ¬ Conjecture35 := by
  intro h
  have h1 := h (Fin 18) G G_connected
  rw [minDegree_G, orderAut_G] at h1
  have h2 : (G.indepNum : ℝ) ≤ 4 := by exact_mod_cast indep_card_le G 3 nonnbr_le
  have h3 : ((14 : ℕ) : ℝ) = 14 := by norm_num
  rw [h3, ceil_tan_fourteen] at h1
  push_cast at h1
  linarith

end GBP421_035

#print axioms GBP421_035.not_conjecture35
