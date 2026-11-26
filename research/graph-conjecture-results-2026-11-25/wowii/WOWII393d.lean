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
# WOWII Conjecture 393d is false

Written on the Wall II (Graffiti.pc, E. DeLaViña), Conjecture 393d (Jan. 2010, status `O`):

> If G is a connected graph on n > 2 vertices, then
> γ₂ ≤ μ(G[V − N(N(P))]) + α(G[V − M]) + |M₄|,
> where P is the set of pendants, M is the set of maximum degree vertices and M₄ is the set of
> vertices each of which is incident with the maximum number of K₄.

(The entry carries the note "If minimum degree is greater than one, then this follows
trivially", copied from 393a–c; our counterexample has two pendants, so it is irrelevant here.)

Definitions: `γ₂` (def 90), `N(S)` (def 46), `μ` matching number (def 2), `α` independence
number, `G[S]` induced subgraph.

Counterexample: graph6 `JMUQ[s?q}u?` (11 vertices, 26 edges). Pendants `P = {2, 8}`,
`N(N(P)) = V ∖ {5}`, so `μ(G[{5}]) = 0`; `M = {1,3,4,6,7,9,10}`, `α(G[{0,2,5,8}]) = 3`;
vertex 4 is the unique vertex in the maximum number (6) of `K₄`s, so `|M₄| = 1`; but `γ₂ = 5`.
-/

namespace WOWII393d

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

/-- Matching number of the induced subgraph `G[S]`. -/
noncomputable def muIn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sSup {k | ∃ M : Finset (Sym2 V), IsMatchingSet G M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ S) ∧ M.card = k}

/-- Independence number of the induced subgraph `G[S]`. -/
noncomputable def alphaIn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sSup {k | ∃ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧ I.card = k}

/-- `N(S)`: vertices adjacent to at least one vertex of `S`. -/
def nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter (fun v => ∃ u ∈ S, G.Adj u v)

/-- Pendant vertices. -/
def pendants (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => G.degree v = 1)

/-- Vertices of maximum degree. -/
def maxDegSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => ∀ u, G.degree u ≤ G.degree v)

/-- Number of `K₄`s containing `v`. -/
def k4Count (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ((univ : Finset V).powersetCard 4 |>.filter
    (fun s => v ∈ s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y)).card

/-- `M₄`: vertices incident with the maximum number of `K₄`s. -/
def maxK4Set (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter (fun v => ∀ u, k4Count G u ≤ k4Count G v)

/-- WOWII Conjecture 393d, as printed. -/
def Conjecture393d : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card W →
      gamma2 G ≤ muIn G (univ \ nbhd G (nbhd G (pendants G))) + alphaIn G (univ \ maxDegSet G)
        + (maxK4Set G).card

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

/-- A matching all of whose edges lie inside `K` has at most `|K| / 2` edges. -/
lemma IsMatchingSet.card_le_half {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : IsMatchingSet G M) (K : Finset V) (hK : ∀ e ∈ M, ∀ v ∈ e, v ∈ K) :
    M.card ≤ K.card / 2 := by
  have h := hM.card_le_cert ∅ {K} (fun a b hab =>
    Or.inr ⟨K, mem_singleton_self K, hK _ hab a (Sym2.mem_mk_left a b),
      hK _ hab b (Sym2.mem_mk_right a b)⟩)
  simpa using h

lemma muIn_le_half (G : SimpleGraph V) (S : Finset V) : muIn G S ≤ S.card / 2 := by
  apply csSup_le
  · exact ⟨0, ∅, ⟨by simp, by simp⟩, by simp, rfl⟩
  · rintro m ⟨M, hM, hS, rfl⟩
    exact hM.card_le_half S hS

lemma alphaIn_le (G : SimpleGraph V) (S : Finset V) (k : ℕ)
    (h : ∀ I ∈ S.powerset, (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) → I.card ≤ k) : alphaIn G S ≤ k := by
  apply csSup_le
  · exact ⟨0, ∅, empty_subset _, by simp, rfl⟩
  · rintro m ⟨I, hIS, hI, rfl⟩
    exact h I (mem_powerset.2 hIS) hI

/-! ### The counterexample -/

/-- Edge list of the graph with graph6 code `JMUQ[s?q}u?`. -/
def edges : List (Fin 11 × Fin 11) :=
  [(0, 3), (0, 5), (0, 7), (0, 9), (0, 10), (1, 2), (1, 3), (1, 4), (1, 6), (1, 9), (1, 10),
   (3, 4), (3, 5), (3, 7), (3, 10), (4, 6), (4, 7), (4, 9), (4, 10), (5, 6), (6, 7), (6, 9),
   (6, 10), (7, 9), (7, 10), (8, 9)]

def G : SimpleGraph (Fin 11) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 11, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have h : ∀ v : Fin 11, G.Reachable 0 v := by
    have r3 : G.Reachable 0 3 := a 0 3 (by decide)
    have r9 : G.Reachable 0 9 := a 0 9 (by decide)
    have r1 : G.Reachable 0 1 := r3.trans (a 3 1 (by decide))
    intro v
    fin_cases v
    · exact Reachable.refl _
    · exact r1
    · exact r1.trans (a 1 2 (by decide))
    · exact r3
    · exact r3.trans (a 3 4 (by decide))
    · exact a 0 5 (by decide)
    · exact r1.trans (a 1 6 (by decide))
    · exact a 0 7 (by decide)
    · exact r9.trans (a 9 8 (by decide))
    · exact r9
    · exact a 0 10 (by decide)
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

/-- Vertex set from a bit vector. -/
def ofBits (b : Fin 11 → Bool) : Finset (Fin 11) := univ.filter (fun i => b i)

/-- No set of at most four vertices 2-dominates `G` (exhaustive over all 2048 vertex sets). -/
lemma twoDom_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    IsTwoDominating G (ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]) →
      5 ≤ (ofBits ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]).card := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_card : ∀ D : Finset (Fin 11), IsTwoDominating G D → 5 ≤ D.card := by
  intro D hD
  have hD' : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D),
      decide (4 ∈ D), decide (5 ∈ D), decide (6 ∈ D), decide (7 ∈ D), decide (8 ∈ D),
      decide (9 ∈ D), decide (10 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits]
  have := twoDom_bits _ _ _ _ _ _ _ _ _ _ _ (hD'.symm ▸ hD)
  rwa [hD'] at this

lemma gamma2_G : 5 ≤ gamma2 G := le_gamma2 G 5 twoDom_card

lemma nnp_G : (univ \ nbhd G (nbhd G (pendants G))) = {5} := by
  decide +kernel

lemma muIn_G : muIn G (univ \ nbhd G (nbhd G (pendants G))) = 0 := by
  rw [nnp_G]
  have := muIn_le_half G {5}
  simp at this
  omega

lemma maxDeg_G : (univ \ maxDegSet G) = {0, 2, 5, 8} := by
  decide +kernel

lemma alphaIn_G : alphaIn G (univ \ maxDegSet G) ≤ 3 := by
  rw [maxDeg_G]
  apply alphaIn_le
  decide +kernel

lemma k4_values :
    (List.finRange 11).map (k4Count G) = [1, 3, 0, 3, 6, 0, 4, 4, 0, 2, 5] := by
  decide +kernel

lemma maxK4_G : (maxK4Set G).card = 1 := by
  decide +kernel

/-- **WOWII Conjecture 393d is false.** -/
theorem not_conjecture393d : ¬ Conjecture393d := by
  intro h
  have h1 := h (Fin 11) G G_connected (by simp)
  rw [muIn_G, maxK4_G] at h1
  have := gamma2_G
  have := alphaIn_G
  omega

end WOWII393d

#print axioms WOWII393d.not_conjecture393d
