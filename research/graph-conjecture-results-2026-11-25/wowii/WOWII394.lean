import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# WOWII Conjecture 394 is false

Written on the Wall II (Graffiti.pc, E. DeLaViña), Conjecture 394 (Jan. 2010, status `O`):

> If G is a connected graph on n > 2 vertices, then γ₂ ≤ μ(G) + |E(G[A₂])| + |M|,
> where M is the set of vertices of min local independence and A₂ is the set of vertices of
> degree two.

Definitions (WOWII defs 90, 4, 100, 2): `γ₂` is the 2-domination number (every vertex outside
`D` has at least two neighbours in `D`); `λ(v)` (local independence) is the independence
number of `G[N(v)]`; `μ` is the matching number; `G[S]` is the induced subgraph.

Counterexample: graph6 `Kgcgg@@?GU?D` (12 vertices, 16 edges): `γ₂ = 7`, `μ = 5`, no two
degree-2 vertices are adjacent, and exactly one vertex attains `λ_min = 1`; so `7 > 5 + 0 + 1`.
-/

namespace WOWII394

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `D` is a 2-dominating set: every vertex outside `D` has at least two neighbours in `D`. -/
def IsTwoDominating (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ (D.filter (G.Adj v)).card

/-- The 2-domination number `γ₂(G)`. -/
noncomputable def gamma2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = k}

/-- `M` is a matching of `G`: a set of edges of `G`, pairwise vertex-disjoint. -/
def IsMatchingSet (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

/-- The matching number `μ(G)`. -/
noncomputable def mu (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ M : Finset (Sym2 V), IsMatchingSet G M ∧ M.card = k}

/-- Local independence `λ(v)`: the independence number of the subgraph induced by `N(v)`. -/
def localIndep (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ((G.neighborFinset v).powerset.filter (fun s => ∀ x ∈ s, ∀ y ∈ s, ¬ G.Adj x y)).sup card

/-- `M`: the set of vertices of minimum local independence. -/
def minLocalIndepSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => ∀ u, localIndep G v ≤ localIndep G u)

/-- `A₂`: the set of vertices of degree two. -/
def degTwoSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => G.degree v = 2)

/-- `|E(G[S])|`: the number of edges of `G` with both endpoints in `S`. -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).card

/-- WOWII Conjecture 394, as printed. -/
def Conjecture394 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card W →
      gamma2 G ≤ mu G + edgesIn G (degTwoSet G) + (minLocalIndepSet G).card

/-! ### General lemmas -/

lemma le_gamma2 (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ D : Finset V, IsTwoDominating G D → k ≤ D.card) : k ≤ gamma2 G := by
  apply le_csInf
  · exact ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  · rintro m ⟨D, hD, rfl⟩
    exact h D hD

lemma mu_le (G : SimpleGraph V) (k : ℕ)
    (h : ∀ M : Finset (Sym2 V), IsMatchingSet G M → M.card ≤ k) : mu G ≤ k := by
  apply csSup_le
  · exact ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  · rintro m ⟨M, hM, rfl⟩
    exact h M hM

/-- Sub-matchings are matchings. -/
lemma IsMatchingSet.mono {G : SimpleGraph V} {M N : Finset (Sym2 V)} (h : IsMatchingSet G M)
    (hNM : N ⊆ M) : IsMatchingSet G N :=
  ⟨fun e he => h.1 e (hNM he), fun e he f hf => h.2 e (hNM he) f (hNM hf)⟩

/-- To bound `μ(G) ≤ k` it suffices to check that no `(k+1)`-subset of the edge set is a
matching. -/
lemma mu_le_of_powersetCard (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ M ∈ G.edgeFinset.powersetCard (k + 1), ¬ IsMatchingSet G M) : mu G ≤ k := by
  apply mu_le
  intro M hM
  by_contra hlt
  push Not at hlt
  obtain ⟨N, hNM, hN⟩ := exists_subset_card_eq (show k + 1 ≤ M.card by omega)
  apply h N _ (hM.mono hNM)
  rw [mem_powersetCard]
  refine ⟨fun e he => ?_, hN⟩
  rw [mem_edgeFinset]
  exact hM.1 e (hNM he)


/-- Tutte–Berge style certificate: if every edge of the matching meets `S` or lies inside one of the sets in
`Ks`, then every matching has at most `|S| + Σ_{K ∈ Ks} ⌊|K|/2⌋` edges. -/
lemma IsMatchingSet.card_le_cert {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : IsMatchingSet G M) (S : Finset V) (Ks : Finset (Finset V))
    (hcov : ∀ a b, s(a, b) ∈ M → (a ∈ S ∨ b ∈ S) ∨ ∃ K ∈ Ks, a ∈ K ∧ b ∈ K) :
    M.card ≤ S.card + ∑ K ∈ Ks, K.card / 2 := by
  classical
  have hsub : M ⊆ (S.biUnion fun s => M.filter (fun e => s ∈ e)) ∪
      Ks.biUnion (fun K => M.filter (fun e => ∀ v ∈ e, v ∈ K)) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rcases hcov a b he with (ha | hb) | ⟨K, hK, ha, hb⟩
      · exact mem_union_left _ (mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨he, Sym2.mem_mk_left a b⟩⟩)
      · exact mem_union_left _ (mem_biUnion.2 ⟨b, hb, mem_filter.2 ⟨he, Sym2.mem_mk_right a b⟩⟩)
      · refine mem_union_right _ (mem_biUnion.2 ⟨K, hK, mem_filter.2 ⟨he, ?_⟩⟩)
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
  have h1 : ∀ s, (M.filter (fun e => s ∈ e)).card ≤ 1 := by
    intro s
    rw [card_le_one]
    intro e he f hf
    rw [mem_filter] at he hf
    by_contra hne
    exact hM.2 e he.1 f hf.1 hne s he.2 hf.2
  have h2 : ∀ K : Finset V, (M.filter (fun e => ∀ v ∈ e, v ∈ K)).card ≤ K.card / 2 := by
    intro K
    set MK := M.filter (fun e => ∀ v ∈ e, v ∈ K)
    have hdisj : ∀ e ∈ MK, ∀ f ∈ MK, e ≠ f → Disjoint e.toFinset f.toFinset := by
      intro e he f hf hef
      rw [mem_filter] at he hf
      rw [Finset.disjoint_left]
      intro x hxe hxf
      rw [Sym2.mem_toFinset] at hxe hxf
      exact hM.2 e he.1 f hf.1 hef x hxe hxf
    have hcard2 : ∀ e ∈ MK, e.toFinset.card = 2 := by
      intro e he
      rw [mem_filter] at he
      exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (hM.1 e he.1))
    have hle : (MK.biUnion Sym2.toFinset).card ≤ K.card := by
      apply card_le_card
      intro x hx
      rw [mem_biUnion] at hx
      obtain ⟨e, he, hxe⟩ := hx
      rw [mem_filter] at he
      exact he.2 x (Sym2.mem_toFinset.1 hxe)
    have hsum : 2 * MK.card = (MK.biUnion Sym2.toFinset).card := by
      rw [card_biUnion hdisj, sum_congr rfl hcard2, sum_const, smul_eq_mul, mul_comm]
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  calc M.card ≤ _ := card_le_card hsub
    _ ≤ (S.biUnion fun s => M.filter (fun e => s ∈ e)).card +
        (Ks.biUnion (fun K => M.filter (fun e => ∀ v ∈ e, v ∈ K))).card := card_union_le _ _
    _ ≤ (∑ s ∈ S, (M.filter (fun e => s ∈ e)).card) +
        ∑ K ∈ Ks, (M.filter (fun e => ∀ v ∈ e, v ∈ K)).card :=
        Nat.add_le_add card_biUnion_le card_biUnion_le
    _ ≤ (∑ s ∈ S, 1) + ∑ K ∈ Ks, K.card / 2 :=
        Nat.add_le_add (sum_le_sum fun s _ => h1 s) (sum_le_sum fun K _ => h2 K)
    _ = S.card + ∑ K ∈ Ks, K.card / 2 := by simp

/-! ### The counterexample -/

/-- Edge list of the graph with graph6 code `Kgcgg@@?GU?D`. -/
def edges : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 4), (1, 2), (1, 8), (2, 5), (3, 4), (3, 6), (4, 5), (4, 10), (5, 6), (6, 10),
   (7, 8), (7, 10), (8, 9), (8, 11), (10, 11)]

def G : SimpleGraph (Fin 12) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 12, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have h : ∀ v : Fin 12, G.Reachable 0 v := by
    have r1 : G.Reachable 0 1 := a 0 1 (by decide)
    have r4 : G.Reachable 0 4 := a 0 4 (by decide)
    have r8 : G.Reachable 0 8 := r1.trans (a 1 8 (by decide))
    have r10 : G.Reachable 0 10 := r4.trans (a 4 10 (by decide))
    intro v
    fin_cases v
    · exact Reachable.refl _
    · exact r1
    · exact r1.trans (a 1 2 (by decide))
    · exact r4.trans (a 4 3 (by decide))
    · exact r4
    · exact r4.trans (a 4 5 (by decide))
    · exact r10.trans (a 10 6 (by decide))
    · exact r8.trans (a 8 7 (by decide))
    · exact r8
    · exact r8.trans (a 8 9 (by decide))
    · exact r10
    · exact r8.trans (a 8 11 (by decide))
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

/-- Vertex set from a bit vector. -/
def ofBits (b : Fin 12 → Bool) : Finset (Fin 12) := univ.filter (fun i => b i)

/-- No set of at most six vertices 2-dominates `G` (exhaustive over all 4096 vertex sets,
enumerated as 12 nested Boolean choices and checked by the kernel). -/
lemma twoDom_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    IsTwoDominating G (ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) →
      7 ≤ (ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]).card := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_card : ∀ D : Finset (Fin 12), IsTwoDominating G D → 7 ≤ D.card := by
  intro D hD
  have hD' : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D), decide (8 ∈ D),
      decide (9 ∈ D), decide (10 ∈ D), decide (11 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits]
  have := twoDom_bits _ _ _ _ _ _ _ _ _ _ _ _ (hD'.symm ▸ hD)
  rwa [hD'] at this

lemma gamma2_G : 7 ≤ gamma2 G := le_gamma2 G 7 twoDom_card

/-- Certificate for `μ(G) ≤ 5`: deleting `S = {8, 10}` leaves the components `{7}`, `{9}`,
`{11}` and `{0,…,6}`, so `μ ≤ 2 + 0 + 0 + 0 + 3`. -/
lemma cover : ∀ a b : Fin 12, G.Adj a b → (a ∈ ({8, 10} : Finset (Fin 12)) ∨
    b ∈ ({8, 10} : Finset (Fin 12))) ∨ ∃ K ∈ ({{7}, {9}, {11}, {0, 1, 2, 3, 4, 5, 6}} :
      Finset (Finset (Fin 12))), a ∈ K ∧ b ∈ K := by
  decide +kernel

lemma mu_G : mu G ≤ 5 := by
  apply mu_le
  intro M hM
  have h := hM.card_le_cert _ _ (fun a b hab => cover a b (hM.1 _ hab))
  have hs : (({8, 10} : Finset (Fin 12)).card + ∑ K ∈ ({{7}, {9}, {11}, {0, 1, 2, 3, 4, 5, 6}} :
      Finset (Finset (Fin 12))), K.card / 2) = 5 := by decide +kernel
  omega

lemma edgesIn_G : edgesIn G (degTwoSet G) = 0 := by
  decide +kernel

lemma minLocalIndep_G : (minLocalIndepSet G).card = 1 := by
  decide +kernel

/-- **WOWII Conjecture 394 is false.** -/
theorem not_conjecture394 : ¬ Conjecture394 := by
  intro h
  have h1 := h (Fin 12) G G_connected (by simp)
  rw [edgesIn_G, minLocalIndep_G] at h1
  have := gamma2_G
  have := mu_G
  omega

end WOWII394

#print axioms WOWII394.not_conjecture394
