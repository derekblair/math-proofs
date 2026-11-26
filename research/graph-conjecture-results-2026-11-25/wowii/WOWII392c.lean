import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.VecNotation

/-!
# WOWII Conjecture 392c is false

*Written on the Wall II* (Graffiti.pc, E. DeLaViña), Conjecture 392c (status `O`):

> If G is a connected graph on n > 2 vertices, then γ₂(G) ≤ μ(G[V − Aδ]) + |Aδ| + κv(G),
> where Aδ is the set of vertices of minimum degree and κv(G) is the number of cut vertices.

(γ₂ 2-domination number, def. 90; μ matching number, def. 2; κv number of cut vertices, def. 106.)

Counterexample: graph6 `N???C@?GC_AGQ?aGMq?` (15 vertices, 18 edges). Aδ = {5, 6} (the two
pendants), vertex 14 is the only cut vertex, μ(G[V − Aδ]) ≤ ⌊13/2⌋ = 6, so the right-hand side
is at most 6 + 2 + 1 = 9; but γ₂ = 10.
-/

namespace WOWII392c

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `D` is 2-dominating: every vertex outside `D` has at least two neighbours in `D`. -/
def IsTwoDominating (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ #(D.filter (G.Adj v))

/-- The 2-domination number `γ₂(G)` (WOWII def. 90). -/
noncomputable def twoDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ D : Finset V, IsTwoDominating G D ∧ #D = k}

/-- The set `Aδ` of vertices of minimum degree. -/
def minDegSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ u, G.degree v ≤ G.degree u

/-- `IsMatchingIn G S k`: there are `k` edges of `G` with all `2k` endpoints distinct and in `S`. -/
def IsMatchingIn (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V × V, (∀ i, G.Adj (f i).1 (f i).2 ∧ (f i).1 ∈ S ∧ (f i).2 ∈ S) ∧
    Function.Injective (Sum.elim (fun i => (f i).1) (fun i => (f i).2))

/-- `μ(G[S])`, the matching number of the subgraph induced by `S` (WOWII def. 2). -/
noncomputable def matchingNumberOn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  sSup {k | IsMatchingIn G S k}

lemma le_twoDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ D : Finset V, IsTwoDominating G D → k ≤ #D) : k ≤ twoDominationNumber G := by
  apply le_csInf
  · exact ⟨_, univ, fun v hv => absurd (mem_univ v) hv, rfl⟩
  · rintro m ⟨D, hD, rfl⟩
    exact h D hD

lemma two_mul_matchingNumberOn_le (G : SimpleGraph V) (S : Finset V) :
    2 * matchingNumberOn G S ≤ #S := by
  have hle : ∀ k ∈ {k | IsMatchingIn G S k}, 2 * k ≤ #S := by
    rintro k ⟨f, hf, hinj⟩
    let g : Fin k ⊕ Fin k → S := fun x => ⟨Sum.elim (fun i => (f i).1) (fun i => (f i).2) x, by
      rcases x with i | i
      · exact (hf i).2.1
      · exact (hf i).2.2⟩
    have hg : Function.Injective g := by
      intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    have := Fintype.card_le_of_injective g hg
    simpa [Fintype.card_sum, two_mul] using this
  have hne : ({k | IsMatchingIn G S k} : Set ℕ).Nonempty :=
    ⟨0, fun i => i.elim0, fun i => i.elim0, fun x => by rcases x with x | x <;> exact x.elim0⟩
  have hbdd : BddAbove {k | IsMatchingIn G S k} :=
    ⟨#S, fun k hk => by have := hle k hk; omega⟩
  exact hle _ (Nat.sSup_mem hne hbdd)

lemma matchingNumberOn_eq_zero (G : SimpleGraph V) (S : Finset V)
    (h : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) : matchingNumberOn G S = 0 := by
  have : {k | IsMatchingIn G S k} = {0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, hf, -⟩
      by_contra hk
      obtain ⟨h1, h2, h3⟩ := hf ⟨0, by omega⟩
      exact h _ h2 _ h3 h1
    · rintro rfl
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun x => by rcases x with x | x <;> exact x.elim0⟩
  rw [matchingNumberOn, this, csSup_singleton]

/-- A vertex of degree at most one lies in every 2-dominating set. -/
lemma mem_of_twoDom_of_degree_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : Finset V} (hD : IsTwoDominating G D) {v : V} (hv : G.degree v ≤ 1) : v ∈ D := by
  by_contra h
  have h2 := hD v h
  have : #(D.filter (G.Adj v)) ≤ G.degree v := by
    rw [← card_neighborFinset_eq_degree]
    apply card_le_card
    intro x hx
    simp only [mem_filter] at hx
    simpa using hx.2
  omega

/-- `v` is a cut vertex: two other vertices are joined only by walks through `v`
(for connected graphs: deleting `v` increases the number of components). -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : V, a ≠ v ∧ b ≠ v ∧ G.Reachable a b ∧ ∀ p : G.Walk a b, v ∈ p.support

open Classical in
/-- κv(G), the number of cut vertices. -/
noncomputable def cardCutVertices (G : SimpleGraph V) : ℕ := #(univ.filter (IsCutVertex G))

/-- WOWII Conjecture 392c. -/
def Conjecture392c : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card W →
      twoDominationNumber G ≤
        matchingNumberOn G (univ \ minDegSet G) + #(minDegSet G) + cardCutVertices G

/-- Parent-pointer certificate: every vertex `≠ v` has a walk to `r` avoiding `v`. -/
lemma walk_avoid (G : SimpleGraph V) (v r : V) (par : V → V) (d : V → ℕ) (hr : r ≠ v)
    (h : ∀ a, a ≠ v → a ≠ r → par a ≠ v ∧ G.Adj a (par a) ∧ d (par a) < d a) :
    ∀ a, a ≠ v → ∃ p : G.Walk a r, v ∉ p.support := by
  suffices H : ∀ m, ∀ a, d a = m → a ≠ v → ∃ p : G.Walk a r, v ∉ p.support from
    fun a => H _ a rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a hm hav
    by_cases har : a = r
    · subst har
      refine ⟨Walk.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton]
      exact fun e => hav e.symm
    · obtain ⟨h1, h2, h3⟩ := h a hav har
      obtain ⟨p, hp⟩ := ih _ (hm ▸ h3) (par a) rfl h1
      refine ⟨Walk.cons h2 p, ?_⟩
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun e => hav e.symm, hp⟩

lemma not_isCutVertex (G : SimpleGraph V) (v r : V) (par : V → V) (d : V → ℕ) (hr : r ≠ v)
    (h : ∀ a, a ≠ v → a ≠ r → par a ≠ v ∧ G.Adj a (par a) ∧ d (par a) < d a) :
    ¬ IsCutVertex G v := by
  rintro ⟨a, b, ha, hb, -, hall⟩
  obtain ⟨p, hp⟩ := walk_avoid G v r par d hr h a ha
  obtain ⟨q, hq⟩ := walk_avoid G v r par d hr h b hb
  have := hall (p.append q.reverse)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at this
  tauto

/-! ### The counterexample -/

def edges : List (Fin 15 × Fin 15) :=
  [(0, 7), (0, 10), (0, 13), (1, 8), (1, 12), (1, 14), (2, 9), (2, 14), (3, 10), (3, 11), (3, 14), (4, 12), (4, 13), (5, 14), (6, 14), (7, 11), (8, 13), (9, 14)]

def G : SimpleGraph (Fin 15) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 15, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r1 : G.Reachable 14 1 := (Reachable.refl 14).trans (a 14 1 (by decide))
  have r2 : G.Reachable 14 2 := (Reachable.refl 14).trans (a 14 2 (by decide))
  have r3 : G.Reachable 14 3 := (Reachable.refl 14).trans (a 14 3 (by decide))
  have r5 : G.Reachable 14 5 := (Reachable.refl 14).trans (a 14 5 (by decide))
  have r6 : G.Reachable 14 6 := (Reachable.refl 14).trans (a 14 6 (by decide))
  have r9 : G.Reachable 14 9 := (Reachable.refl 14).trans (a 14 9 (by decide))
  have r8 : G.Reachable 14 8 := r1.trans (a 1 8 (by decide))
  have r12 : G.Reachable 14 12 := r1.trans (a 1 12 (by decide))
  have r10 : G.Reachable 14 10 := r3.trans (a 3 10 (by decide))
  have r11 : G.Reachable 14 11 := r3.trans (a 3 11 (by decide))
  have r13 : G.Reachable 14 13 := r8.trans (a 8 13 (by decide))
  have r4 : G.Reachable 14 4 := r12.trans (a 12 4 (by decide))
  have r0 : G.Reachable 14 0 := r10.trans (a 10 0 (by decide))
  have r7 : G.Reachable 14 7 := r11.trans (a 11 7 (by decide))
  have h : ∀ v : Fin 15, G.Reachable 14 v := by
    intro v
    fin_cases v
    · exact r0
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
    · exact Reachable.refl _
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

def parT : Fin 15 → Fin 15 → Fin 15 := ![![0, 14, 14, 14, 12, 14, 14, 11, 1, 14, 3, 3, 1, 8, 14], ![10, 1, 14, 14, 13, 14, 14, 11, 13, 14, 3, 3, 4, 0, 14], ![10, 14, 2, 14, 12, 14, 14, 11, 1, 14, 3, 3, 1, 8, 14], ![13, 14, 14, 3, 12, 14, 14, 0, 1, 14, 0, 7, 1, 8, 14], ![10, 14, 14, 14, 4, 14, 14, 11, 1, 14, 3, 3, 1, 8, 14], ![10, 14, 14, 14, 12, 5, 14, 11, 1, 14, 3, 3, 1, 8, 14], ![10, 14, 14, 14, 12, 14, 6, 11, 1, 14, 3, 3, 1, 8, 14], ![10, 14, 14, 14, 12, 14, 14, 7, 1, 14, 3, 3, 1, 8, 14], ![10, 14, 14, 14, 12, 14, 14, 11, 8, 14, 3, 3, 1, 4, 14], ![10, 14, 14, 14, 12, 14, 14, 11, 1, 9, 3, 3, 1, 8, 14], ![13, 14, 14, 14, 12, 14, 14, 11, 1, 14, 10, 3, 1, 8, 14], ![10, 14, 14, 14, 12, 14, 14, 0, 1, 14, 3, 11, 1, 8, 14], ![10, 14, 14, 14, 13, 14, 14, 11, 1, 14, 3, 3, 12, 8, 14], ![10, 14, 14, 14, 12, 14, 14, 11, 1, 14, 3, 3, 1, 13, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]

def depT : Fin 15 → Fin 15 → ℕ := ![![0, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3, 0], ![3, 0, 1, 1, 5, 1, 1, 3, 5, 1, 2, 2, 6, 4, 0], ![3, 1, 0, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 3, 0], ![4, 1, 1, 0, 3, 1, 1, 5, 2, 1, 5, 6, 2, 3, 0], ![3, 1, 1, 1, 0, 1, 1, 3, 2, 1, 2, 2, 2, 3, 0], ![3, 1, 1, 1, 3, 0, 1, 3, 2, 1, 2, 2, 2, 3, 0], ![3, 1, 1, 1, 3, 1, 0, 3, 2, 1, 2, 2, 2, 3, 0], ![3, 1, 1, 1, 3, 1, 1, 0, 2, 1, 2, 2, 2, 3, 0], ![3, 1, 1, 1, 3, 1, 1, 3, 0, 1, 2, 2, 2, 4, 0], ![3, 1, 1, 1, 3, 1, 1, 3, 2, 0, 2, 2, 2, 3, 0], ![4, 1, 1, 1, 3, 1, 1, 3, 2, 1, 0, 2, 2, 3, 0], ![3, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 0, 2, 3, 0], ![3, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 0, 3, 0], ![3, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def rootT : Fin 15 → Fin 15 := ![14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0]

lemma cut_cert : ∀ v : Fin 15, v ≠ 14 → rootT v ≠ v ∧
    ∀ a, a ≠ v → a ≠ rootT v → parT v a ≠ v ∧ G.Adj a (parT v a) ∧ depT v (parT v a) < depT v a := by
  decide +kernel

lemma cardCut_le : cardCutVertices G ≤ 1 := by
  classical
  unfold cardCutVertices
  have : univ.filter (IsCutVertex G) ⊆ {14} := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    by_contra hne
    have hne' : v ≠ 14 := by simpa using hne
    obtain ⟨hr, hc⟩ := cut_cert v hne'
    exact not_isCutVertex G v (rootT v) (parT v) (depT v) hr hc hv
  exact (card_le_card this).trans (by simp)

lemma minDeg_G : minDegSet G = {5, 6} := by
  decide +kernel

lemma mu_le : matchingNumberOn G (univ \ minDegSet G) ≤ 6 := by
  have := two_mul_matchingNumberOn_le G (univ \ minDegSet G)
  rw [minDeg_G] at this ⊢
  have h13 : #(univ \ ({5, 6} : Finset (Fin 15))) = 13 := by decide
  omega

def ofBits (b : Fin 15 → Bool) : Finset (Fin 15) := univ.filter (fun i => b i)

lemma twoDom_bits_0 : ∀ b2 b3 b4 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![false, false, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) → 10 ≤ #(ofBits ![false, false, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_1 : ∀ b2 b3 b4 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![false, true, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) → 10 ≤ #(ofBits ![false, true, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_2 : ∀ b2 b3 b4 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![true, false, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) → 10 ≤ #(ofBits ![true, false, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_3 : ∀ b2 b3 b4 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![true, true, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) → 10 ≤ #(ofBits ![true, true, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits : ∀ b0 b1 b2 b3 b4 b7 b8 b9 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![b0, b1, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) → 10 ≤ #(ofBits ![b0, b1, b2, b3, b4, true, true, b7, b8, b9, b10, b11, b12, b13, b14]) := by
  intro b0 b1
  cases b0 <;> cases b1
  · exact twoDom_bits_0
  · exact twoDom_bits_1
  · exact twoDom_bits_2
  · exact twoDom_bits_3

lemma le_twoDom : 10 ≤ twoDominationNumber G := by
  apply le_twoDominationNumber
  intro D hD
  have h5 : (5 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h6 : (6 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have e : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D), decide (4 ∈ D), true, true, decide (7 ∈ D), decide (8 ∈ D), decide (9 ∈ D), decide (10 ∈ D), decide (11 ∈ D), decide (12 ∈ D), decide (13 ∈ D), decide (14 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits, h5, h6]
  have := twoDom_bits (decide (0 ∈ D)) (decide (1 ∈ D)) (decide (2 ∈ D)) (decide (3 ∈ D)) (decide (4 ∈ D)) (decide (7 ∈ D)) (decide (8 ∈ D)) (decide (9 ∈ D)) (decide (10 ∈ D)) (decide (11 ∈ D)) (decide (12 ∈ D)) (decide (13 ∈ D)) (decide (14 ∈ D)) (e.symm ▸ hD)
  rwa [e] at this

/-- **WOWII Conjecture 392c is false.** -/
theorem not_conjecture392c : ¬ Conjecture392c := by
  intro h
  have h1 := h (Fin 15) G G_connected (by simp)
  have h2 := le_twoDom
  have h3 := mu_le
  have h4 := cardCut_le
  rw [minDeg_G] at h1 h3
  have h5 : #({5, 6} : Finset (Fin 15)) = 2 := by decide
  omega

end WOWII392c

#print axioms WOWII392c.not_conjecture392c
