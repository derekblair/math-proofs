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
# WOWII Conjecture 395a is false

*Written on the Wall II* (Graffiti.pc, E. DeLaViña), Conjecture 395a (status `O`):

> If G is a connected graph on n > 2 vertices, then γ₂(G) ≤ |M| + μ(G[V − Aδ]) + μ(G[N(A2)]),
> where M is the set of vertices of modemin degree, Aδ is the set of minimum degree vertices
> and A2 is the set of vertices of degree two.

(γ₂ 2-domination number, def. 90; μ matching number, def. 2; mode_min = the smallest most
frequent degree.)

Counterexample: graph6 `N???????C?[?w?[?B~?` (15 vertices, 18 edges). Degree sequence
`1⁶ 2² 3⁶ 8`, so mode_min = 1 and M = Aδ = the six pendants `{4,…,9}`; μ(G[V − Aδ]) ≤ ⌊9/2⌋ = 4;
A2 = {3, 10} and N(A2) = {0, 13, 14} is independent, so μ(G[N(A2)]) = 0. The right-hand side is
at most 6 + 4 + 0 = 10, but γ₂ = 11.
-/

namespace WOWII395a

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

/-- Number of vertices of degree `d`. -/
def degCount (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  #(univ.filter fun u => G.degree u = d)

/-- `M`: the vertices whose degree is mode_min, the smallest most frequent degree. -/
def modeMinSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ u, degCount G (G.degree u) ≤ degCount G (G.degree v) ∧
    (degCount G (G.degree u) = degCount G (G.degree v) → G.degree v ≤ G.degree u)

/-- `N(A2)`: the neighbours of the degree-two vertices. -/
def nbrA2 (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ u, G.degree u = 2 ∧ G.Adj u v

/-- WOWII Conjecture 395a. -/
def Conjecture395a : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card W →
      twoDominationNumber G ≤
        #(modeMinSet G) + matchingNumberOn G (univ \ minDegSet G) + matchingNumberOn G (nbrA2 G)

/-! ### The counterexample -/

def edges : List (Fin 15 × Fin 15) :=
  [(0, 10), (0, 11), (0, 12), (1, 11), (1, 12), (1, 13), (2, 11), (2, 12), (2, 13), (3, 13), (3, 14), (4, 14), (5, 14), (6, 14), (7, 14), (8, 14), (9, 14), (10, 14)]

def G : SimpleGraph (Fin 15) := SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

lemma G_connected : G.Connected := by
  have a : ∀ x y : Fin 15, G.Adj x y → G.Reachable x y := fun _ _ h => h.reachable
  have r3 : G.Reachable 14 3 := (Reachable.refl 14).trans (a 14 3 (by decide))
  have r4 : G.Reachable 14 4 := (Reachable.refl 14).trans (a 14 4 (by decide))
  have r5 : G.Reachable 14 5 := (Reachable.refl 14).trans (a 14 5 (by decide))
  have r6 : G.Reachable 14 6 := (Reachable.refl 14).trans (a 14 6 (by decide))
  have r7 : G.Reachable 14 7 := (Reachable.refl 14).trans (a 14 7 (by decide))
  have r8 : G.Reachable 14 8 := (Reachable.refl 14).trans (a 14 8 (by decide))
  have r9 : G.Reachable 14 9 := (Reachable.refl 14).trans (a 14 9 (by decide))
  have r10 : G.Reachable 14 10 := (Reachable.refl 14).trans (a 14 10 (by decide))
  have r13 : G.Reachable 14 13 := r3.trans (a 3 13 (by decide))
  have r0 : G.Reachable 14 0 := r10.trans (a 10 0 (by decide))
  have r1 : G.Reachable 14 1 := r13.trans (a 13 1 (by decide))
  have r2 : G.Reachable 14 2 := r13.trans (a 13 2 (by decide))
  have r11 : G.Reachable 14 11 := r0.trans (a 0 11 (by decide))
  have r12 : G.Reachable 14 12 := r0.trans (a 0 12 (by decide))
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

lemma modeMin_G : #(modeMinSet G) = 6 := by
  unfold modeMinSet degCount
  decide +kernel

lemma minDeg_G : minDegSet G = {4, 5, 6, 7, 8, 9} := by
  decide +kernel

lemma mu1_le : matchingNumberOn G (univ \ minDegSet G) ≤ 4 := by
  have := two_mul_matchingNumberOn_le G (univ \ minDegSet G)
  rw [minDeg_G] at this ⊢
  have h9 : #(univ \ ({4, 5, 6, 7, 8, 9} : Finset (Fin 15))) = 9 := by decide
  omega

lemma nbrA2_indep : ∀ x ∈ nbrA2 G, ∀ y ∈ nbrA2 G, ¬ G.Adj x y := by
  unfold nbrA2
  decide +kernel

lemma mu2 : matchingNumberOn G (nbrA2 G) = 0 := matchingNumberOn_eq_zero G _ nbrA2_indep

def ofBits (b : Fin 15 → Bool) : Finset (Fin 15) := univ.filter (fun i => b i)

lemma twoDom_bits_0 : ∀ b2 b3 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![false, false, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) → 11 ≤ #(ofBits ![false, false, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_1 : ∀ b2 b3 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![false, true, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) → 11 ≤ #(ofBits ![false, true, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_2 : ∀ b2 b3 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![true, false, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) → 11 ≤ #(ofBits ![true, false, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits_3 : ∀ b2 b3 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![true, true, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) → 11 ≤ #(ofBits ![true, true, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) := by
  unfold IsTwoDominating
  decide +kernel

lemma twoDom_bits : ∀ b0 b1 b2 b3 b10 b11 b12 b13 b14 : Bool,
    IsTwoDominating G (ofBits ![b0, b1, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) → 11 ≤ #(ofBits ![b0, b1, b2, b3, true, true, true, true, true, true, b10, b11, b12, b13, b14]) := by
  intro b0 b1
  cases b0 <;> cases b1
  · exact twoDom_bits_0
  · exact twoDom_bits_1
  · exact twoDom_bits_2
  · exact twoDom_bits_3

lemma le_twoDom : 11 ≤ twoDominationNumber G := by
  apply le_twoDominationNumber
  intro D hD
  have h4 : (4 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h5 : (5 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h6 : (6 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h7 : (7 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h8 : (8 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have h9 : (9 : Fin 15) ∈ D := mem_of_twoDom_of_degree_le_one G hD (by decide)
  have e : ofBits ![decide (0 ∈ D), decide (1 ∈ D), decide (2 ∈ D), decide (3 ∈ D), true, true, true, true, true, true, decide (10 ∈ D), decide (11 ∈ D), decide (12 ∈ D), decide (13 ∈ D), decide (14 ∈ D)] = D := by
    ext i
    fin_cases i <;> simp [ofBits, h4, h5, h6, h7, h8, h9]
  have := twoDom_bits (decide (0 ∈ D)) (decide (1 ∈ D)) (decide (2 ∈ D)) (decide (3 ∈ D)) (decide (10 ∈ D)) (decide (11 ∈ D)) (decide (12 ∈ D)) (decide (13 ∈ D)) (decide (14 ∈ D)) (e.symm ▸ hD)
  rwa [e] at this

/-- **WOWII Conjecture 395a is false.** -/
theorem not_conjecture395a : ¬ Conjecture395a := by
  intro h
  have h1 := h (Fin 15) G G_connected (by simp)
  have h2 := le_twoDom
  have h3 := mu1_le
  rw [modeMin_G, mu2] at h1
  omega

end WOWII395a

#print axioms WOWII395a.not_conjecture395a
