import Mathlib

/-!
# Graph Brain Project open lower bounds #15 and #18 on the independence number are false

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), lower bounds for connected graphs:

* #15: `independence_number(x) >= ceil(lovasz_theta(x)) - welsh_powell(x)`
* #18: `independence_number(x) >= minimum(inverse_degree(x), floor(lovasz_theta(x)))`

Definitions (gt.sage):
* `lovasz_theta`: the Lovász theta number, here in its primal SDP form
  `θ(G) = sup { Σᵢⱼ Bᵢⱼ : B ⪰ 0, tr B = 1, Bᵢⱼ = 0 for every edge ij }`.
* `welsh_powell`: `max_i min(i, d_i + 1)` for the degrees sorted `d_1 ≥ … ≥ d_n`.
* `inverse_degree`: `Σ_v 1/d(v)` over vertices of non-zero degree.

Counterexample: `G` = a hub vertex joined to one vertex of each of 26 disjoint 5-cycles
(131 vertices, connected). Then
* `α(G) ≤ 2·26 + 1 = 53` (at most 2 vertices per 5-cycle, plus the hub);
* `θ(G) ≥ 26 · 15881/7129 > 57.9`, certified by an explicit feasible Gram matrix built from
  five integer vectors in `ℤ³` that are orthogonal along the 5-cycle (the hub gets `0`);
* degrees are `26` (hub), `3`, `2`, so `welsh_powell(G) ≤ 4` and
  `inverse_degree(G) = 1/26 + 26/3 + 104/2 > 60`.
Hence #15: `⌈θ⌉ − WP ≥ 58 − 4 = 54 > 53 ≥ α`; #18: `min(invdeg, ⌊θ⌋) ≥ 57 > 53 ≥ α`.
-/

namespace GBP421_015_018

open SimpleGraph Finset Matrix

/-! ### Definitions -/

section defs
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Feasible matrices for the primal SDP of the Lovász theta number. -/
def Feasible (G : SimpleGraph W) (B : Matrix W W ℝ) : Prop :=
  B.PosSemidef ∧ B.trace = 1 ∧ ∀ i j, G.Adj i j → B i j = 0

/-- Lovász theta number (primal SDP formulation). -/
noncomputable def lovaszTheta (G : SimpleGraph W) : ℝ :=
  sSup {x | ∃ B, Feasible G B ∧ x = ∑ i, ∑ j, B i j}

/-- Welsh–Powell bound `max_i min(i, d_i + 1)`, degrees sorted non-increasingly (`i` 1-based). -/
def welshPowell (G : SimpleGraph W) [DecidableRel G.Adj] : ℕ :=
  (((univ.val.map fun v => G.degree v).sort (· ≥ ·)).zipIdx.map fun p => min (p.2 + 1) (p.1 + 1)).foldr max 0

/-- `inverse_degree`: sum of reciprocals of the non-zero degrees. -/
noncomputable def inverseDegree (G : SimpleGraph W) [DecidableRel G.Adj] : ℝ :=
  ∑ v, if G.degree v = 0 then 0 else 1 / (G.degree v : ℝ)

/-- GBP #421 lower bound #15, for connected graphs. -/
def Conjecture15 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → ⌈lovaszTheta G⌉ - (welshPowell G : ℤ) ≤ G.indepNum

/-- GBP #421 lower bound #18, for connected graphs. -/
def Conjecture18 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → min (inverseDegree G) (⌊lovaszTheta G⌋ : ℝ) ≤ G.indepNum

/-! ### Every feasible value is at most `θ` (the feasible set is bounded by `|V|`) -/

lemma quad_le {B : Matrix W W ℝ} (hB : B.PosSemidef) (i j : W) :
    B i j + B j i ≤ B i i + B j j := by
  have h := hB.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [mulVec_sub, dotProduct_sub, sub_dotProduct, mulVec_single, single_dotProduct] at h
  linarith

lemma sum_le_card {B : Matrix W W ℝ} (hB : B.PosSemidef) (ht : B.trace = 1) :
    ∑ i, ∑ j, B i j ≤ Fintype.card W := by
  have h1 : ∑ i, ∑ j, (B i j + B j i) ≤ ∑ i, ∑ j, (B i i + B j j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => quad_le hB i j
  have htr : ∑ i, B i i = 1 := by simpa [Matrix.trace] using ht
  rw [Finset.sum_comm (f := fun i j => B i i + B j j)] at h1
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul] at h1
  rw [Finset.sum_comm (f := fun i j => B j i)] at h1
  rw [htr] at h1
  simp only [← Finset.mul_sum, htr] at h1
  linarith

lemma le_theta (G : SimpleGraph W) {B : Matrix W W ℝ} (hB : Feasible G B) :
    ∑ i, ∑ j, B i j ≤ lovaszTheta G :=
  le_csSup ⟨Fintype.card W, by rintro x ⟨B', hB', rfl⟩; exact sum_le_card hB'.1 hB'.2.1⟩
    ⟨B, hB, rfl⟩

end defs

/-! ### Connectivity from a parent certificate -/

lemma walk_of_parent {V : Type*} (G : SimpleGraph V) (u : V) (f : V → ℕ) (hu : f u = 0)
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
    have h : v ≠ u := by rintro rfl; omega
    obtain ⟨p, hadj, hp'⟩ := hp v h
    obtain ⟨q, hq⟩ := ih p (by omega)
    exact ⟨.cons hadj q, by simp [hq]; omega⟩

/-! ### The graph: hub `none`, 5-cycle vertices `some (p, a)` -/

abbrev V := Option (Fin 26 × Fin 5)

/-- One direction of each edge: hub → `(p,0)`, and `(p,a) → (p,a+1)`. -/
def r : V → V → Bool
  | none, some (_, a) => a == 0
  | some (p, a), some (q, b) => p == q && b == a + 1
  | _, _ => false

def G : SimpleGraph V := SimpleGraph.fromRel fun x y => r x y = true

instance : DecidableRel G.Adj := fun x y => by
  unfold G SimpleGraph.fromRel; simp only; infer_instance

def lvl : V → ℕ
  | none => 0
  | some (_, a) => 1 + ![0, 1, 2, 2, 1] a

lemma cert : lvl none = 0 ∧ ∀ v, v ≠ none → ∃ p, G.Adj v p ∧ lvl p + 1 = lvl v := by
  decide +kernel

lemma G_connected : G.Connected := by
  have hw := walk_of_parent G none lvl cert.1 cert.2
  refine (connected_iff_exists_forall_reachable G).2 ⟨none, fun v => ?_⟩
  obtain ⟨q, -⟩ := hw v
  exact q.reverse.reachable

/-! ### Independence number `≤ 53` -/

lemma five_le_two : ∀ f : Fin 5 → Bool, (∀ a, f a = true → f (a + 1) = true → False) →
    (∑ a, if f a = true then 1 else 0 : ℕ) ≤ 2 := by
  decide

lemma adj_succ (p : Fin 26) (a : Fin 5) : G.Adj (some (p, a)) (some (p, a + 1)) := by
  revert p a; decide +kernel

lemma indepNum_G : G.indepNum ≤ 53 := by
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  rw [← hD.card_eq]
  have hc : D.card = ∑ v, if v ∈ D then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext v; simp
  have hin : ∀ p, (∑ a : Fin 5, if some (p, a) ∈ D then 1 else 0 : ℕ) ≤ 2 := by
    intro p
    have := five_le_two (fun a => decide (some (p, a) ∈ D)) (by
      intro a h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      exact hD.isIndepSet (Finset.mem_coe.2 h1) (Finset.mem_coe.2 h2)
        (G.ne_of_adj (adj_succ p a)) (adj_succ p a))
    simpa using this
  rw [hc, Fintype.sum_option, Fintype.sum_prod_type]
  have h1 : (if (none : V) ∈ D then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> simp
  have h2 : (∑ p : Fin 26, ∑ a : Fin 5, if some (p, a) ∈ D then 1 else 0 : ℕ) ≤ ∑ _p : Fin 26, 2 :=
    Finset.sum_le_sum fun p _ => hin p
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

/-! ### Lovász theta `≥ 26 · 15881 / 7129` -/

/-- Five integer vectors in `ℤ³`, cyclically consecutive ones orthogonal. -/
def wv : Fin 5 → Fin 3 → ℝ :=
  ![![0, -24, 30], ![40, 0, 0], ![0, -39, 0], ![24, 0, 30], ![20, -20, -16]]

def M : Matrix (Fin 3) V ℝ := fun k v =>
  match v with
  | none => 0
  | some (_, a) => wv a k

noncomputable def Bc : Matrix V V ℝ := (1 / (26 * 7129) : ℝ) • (Mᴴ * M)

lemma Bc_apply (i j : V) : Bc i j = 1 / (26 * 7129) * ∑ k, M k i * M k j := by
  simp [Bc, mul_apply]

lemma Bc_psd : Bc.PosSemidef :=
  (posSemidef_conjTranspose_mul_self M).smul (by norm_num)

lemma Bc_trace : Bc.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, Bc_apply]
  simp [Fintype.sum_option, Fintype.sum_prod_type, M, wv, Fin.sum_univ_five, Fin.sum_univ_three]
  norm_num

lemma Bc_edge : ∀ i j, G.Adj i j → Bc i j = 0 := by
  intro i j h
  rcases i with _ | ⟨p, a⟩ <;> rcases j with _ | ⟨q, b⟩
  · exact (G.ne_of_adj h rfl).elim
  · simp [Bc_apply, M]
  · simp [Bc_apply, M]
  · simp only [G, SimpleGraph.fromRel_adj, r] at h
    simp only [ne_eq, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h
    rcases h.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · fin_cases a <;> simp [Bc_apply, M, wv, Fin.sum_univ_three] <;> norm_num
    · fin_cases b <;> simp [Bc_apply, M, wv, Fin.sum_univ_three] <;> norm_num

lemma Bc_feasible : Feasible G Bc := ⟨Bc_psd, Bc_trace, Bc_edge⟩

lemma rowsum (k : Fin 3) : ∑ v, M k v = 26 * ∑ a, wv a k := by
  simp [M, Fintype.sum_option, Fintype.sum_prod_type]

lemma Bc_sum : ∑ i, ∑ j, Bc i j = 26 * 15881 / 7129 := by
  have e : ∀ i j, Bc i j = ∑ k : Fin 3, 1 / (26 * 7129) * (M k i * M k j) := by
    intro i j; rw [Bc_apply, Finset.mul_sum]
  simp only [e]
  have : ∀ i : V, ∑ j : V, ∑ k : Fin 3, 1 / (26 * 7129) * (M k i * M k j) =
      ∑ k : Fin 3, 1 / (26 * 7129) * (M k i * ∑ j, M k j) := by
    intro i; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  simp only [this]
  rw [Finset.sum_comm]
  have h2 : ∀ k : Fin 3, ∑ i : V, 1 / (26 * 7129) * (M k i * ∑ j, M k j) =
      1 / (26 * 7129) * ((∑ i, M k i) * ∑ j, M k j) := by
    intro k; rw [Finset.sum_mul, Finset.mul_sum]
  simp only [h2]
  simp only [rowsum]
  simp [Fin.sum_univ_three, Fin.sum_univ_five, wv]
  norm_num

lemma theta_G : (26 * 15881 / 7129 : ℝ) ≤ lovaszTheta G := Bc_sum ▸ le_theta G Bc_feasible

/-! ### Degrees, Welsh–Powell, inverse degree -/

def dg : V → ℕ
  | none => 26
  | some (_, a) => if a = 0 then 3 else 2

lemma hdeg : ∀ v, G.degree v = dg v := by decide +kernel

/-- Insertion into a non-increasing list (a local copy of `List.orderedInsert (· ≥ ·)`). -/
def insOrd (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≥ b then a :: b :: l else b :: insOrd a l

/-- Insertion sort, non-increasing (a local copy of `List.insertionSort (· ≥ ·)`). -/
def insSort : List ℕ → List ℕ
  | [] => []
  | a :: l => insOrd a (insSort l)

lemma insOrd_eq (a : ℕ) (l : List ℕ) : insOrd a l = l.orderedInsert (· ≥ ·) a := by
  induction l with
  | nil => simp [insOrd, List.orderedInsert_nil]
  | cons b l ih => simp [insOrd, List.orderedInsert_cons, ih]

lemma insSort_eq (l : List ℕ) : insSort l = l.insertionSort (· ≥ ·) := by
  induction l with
  | nil => simp [insSort, List.insertionSort_nil]
  | cons a l ih => simp [insSort, List.insertionSort_cons, ih, insOrd_eq]

/-- `Multiset.sort` (merge sort) computed by insertion sort, which the kernel can evaluate. -/
lemma sort_eq (s : Multiset ℕ) : s.sort (· ≥ ·) = Quot.liftOn s insSort
    (fun a b h => by
      simp only [insSort_eq]
      rw [← List.mergeSort_eq_insertionSort, ← List.mergeSort_eq_insertionSort,
        ← Multiset.coe_sort, ← Multiset.coe_sort, Multiset.coe_eq_coe.2 h]) :=
  Quot.inductionOn s fun l => by
    show List.mergeSort l _ = insSort l
    rw [insSort_eq]; exact List.mergeSort_eq_insertionSort _ l

lemma wp_G : welshPowell G ≤ 4 := by
  unfold welshPowell
  rw [Multiset.map_congr rfl (fun v _ => hdeg v), sort_eq]
  decide +kernel

lemma invdeg_G : (60 : ℝ) ≤ inverseDegree G := by
  unfold inverseDegree
  simp only [hdeg]
  simp [dg, Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_five]
  norm_num

/-! ### Main theorems -/

/-- **Graph Brain Project lower bound #15 (issue #421) is false.** -/
theorem not_conjecture15 : ¬ Conjecture15 := by
  intro h
  have h1 := h V G G_connected
  have hc : (57 : ℤ) < ⌈lovaszTheta G⌉ := by
    rw [Int.lt_ceil]; have := theta_G; push_cast; linarith
  have ha := indepNum_G
  have hw := wp_G
  omega

/-- **Graph Brain Project lower bound #18 (issue #421) is false.** -/
theorem not_conjecture18 : ¬ Conjecture18 := by
  intro h
  have h1 := h V G G_connected
  have hf : (57 : ℤ) ≤ ⌊lovaszTheta G⌋ := by
    rw [Int.le_floor]; have := theta_G; push_cast; linarith
  have hf' : (57 : ℝ) ≤ (⌊lovaszTheta G⌋ : ℝ) := by exact_mod_cast hf
  have ha : (G.indepNum : ℝ) ≤ 53 := by exact_mod_cast indepNum_G
  have hm : (57 : ℝ) ≤ min (inverseDegree G) (⌊lovaszTheta G⌋ : ℝ) :=
    le_min (by linarith [invdeg_G]) hf'
  linarith

end GBP421_015_018

#print axioms GBP421_015_018.not_conjecture15
#print axioms GBP421_015_018.not_conjecture18
