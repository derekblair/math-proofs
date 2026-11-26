import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# An open even-hole-free conjecture of *Automated Conjecturing III* is false

C. E. Larson and N. Van Cleemput, *Automated conjecturing III: property-relations conjectures*,
Ann. Math. Artif. Intell. 81 (2017) 315–327, §3.2, lists as "open sufficient condition conjectures"
for a graph to be even-hole-free:

> `(((is_circular_planar) -> (is_perfect)) -> (is_clique)) -> (is_even_hole_free)`

Here `is_circular_planar` is Sage's outerplanarity test, `is_perfect` means every induced
subgraph `H` has `χ(H) = ω(H)`, `is_clique` means complete, and a *hole* is an induced cycle of
length at least 4.

Counterexample: graph6 `FCpb_` (7 vertices, 8 edges): a 5-cycle `0-3-6-1-4-0` and a 4-cycle
`1-5-2-6-1` sharing the edge `16`. It is outerplanar, it is not perfect (the induced `C₅`
has clique number 2 but is not 2-colourable), so `outerplanar → perfect` is false and the
hypothesis of the conjecture holds vacuously; but `1-5-2-6` is an even hole.
It is the unique smallest connected counterexample (exhaustive check of connected graphs on ≤ 7
vertices).

Definitions used:
* **Outerplanar** via the Bernhart–Kainen characterisation (J. Combin. Theory B 27 (1979)):
  a graph is outerplanar iff it has a one-page book embedding, i.e. an ordering of the vertices
  along a line such that no two edges `ab`, `cd` interleave as `a < c < b < d`.
* **Perfect**: for every vertex set `S`, `G[S]` can be properly coloured with colours
  `0, …, ω(G[S]) − 1`.
* **Hole** of length `k ≥ 4`: an injective `c : Fin k → V` with `c i ~ c j ↔ j = i ± 1 (mod k)`.
-/

namespace AC3EHF

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One-page book embedding (equivalent to outerplanarity, Bernhart–Kainen 1979). -/
def IsOuterplanar (G : SimpleGraph V) : Prop :=
  ∃ p : V → ℕ, Function.Injective p ∧
    ∀ a b c d, G.Adj a b → G.Adj c d → ¬ (p a < p c ∧ p c < p b ∧ p b < p d)

/-- Clique number of `G[S]`. -/
def cliqueNumOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (S.powerset.filter fun T => ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v).sup card

/-- Perfect: every induced subgraph `G[S]` is `ω(G[S])`-colourable. -/
def IsPerfect (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, ∃ c : V → ℕ, (∀ v ∈ S, c v < cliqueNumOn G S) ∧
    ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

/-- Complete graph. -/
def IsCompleteGraph (G : SimpleGraph V) : Prop := ∀ u v, u ≠ v → G.Adj u v

/-- `c` is an induced cycle (a hole) of length `k`. -/
def IsHole (G : SimpleGraph V) {k : ℕ} (c : Fin k → V) : Prop :=
  4 ≤ k ∧ Function.Injective c ∧
    ∀ i j : Fin k, G.Adj (c i) (c j) ↔ ((j : ℕ) = ((i : ℕ) + 1) % k ∨ (i : ℕ) = ((j : ℕ) + 1) % k)

/-- No induced cycle of even length `≥ 4`. -/
def IsEvenHoleFree (G : SimpleGraph V) : Prop :=
  ∀ (k : ℕ) (c : Fin k → V), IsHole G c → ¬ Even k

/-- The conjecture, for (finite) connected graphs. -/
def Conjecture : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    G.Connected →
      ((IsOuterplanar G → IsPerfect G) → IsCompleteGraph G) → IsEvenHoleFree G

/-! ### The counterexample `FCpb_` -/

def E : List (ℕ × ℕ) := [(0, 3), (0, 4), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 6)]

def R (i j : Fin 7) : Prop := ((i : ℕ), (j : ℕ)) ∈ E

instance : DecidableRel R := fun i j => by unfold R; infer_instance

def G : SimpleGraph (Fin 7) := SimpleGraph.fromRel R

instance : DecidableRel G.Adj := fun i j => by
  unfold G SimpleGraph.fromRel; simp only; infer_instance

lemma G_connected : G.Connected := by
  -- path 0-3-6-2-5-1-4 visits every vertex
  have h : ∀ i : Fin 6, G.Adj (![0, 3, 6, 2, 5, 1, 4] i.castSucc) (![0, 3, 6, 2, 5, 1, 4] i.succ) := by
    decide
  refine (connected_iff_exists_forall_reachable G).2 ⟨0, fun v => ?_⟩
  have r : ∀ i : Fin 7, G.Reachable 0 (![0, 3, 6, 2, 5, 1, 4] i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact ih.trans (h i).reachable
  fin_cases v
  · exact r 0
  · exact r 5
  · exact r 3
  · exact r 1
  · exact r 6
  · exact r 4
  · exact r 2

/-- Spine positions along the outer cycle `0,3,6,2,5,1,4`. -/
def pos : Fin 7 → ℕ := ![0, 5, 3, 1, 6, 4, 2]

lemma G_outerplanar : IsOuterplanar G := by
  refine ⟨pos, ?_, ?_⟩
  · intro a b h; revert a b; decide
  · decide

lemma cliqueNum_C5 : cliqueNumOn G {0, 3, 6, 1, 4} = 2 := by decide +kernel

lemma C5_not_two_col : ∀ c : Fin 7 → Fin 2, ∃ u ∈ ({0, 3, 6, 1, 4} : Finset (Fin 7)),
    ∃ v ∈ ({0, 3, 6, 1, 4} : Finset (Fin 7)), G.Adj u v ∧ c u = c v := by
  decide +kernel

lemma G_not_perfect : ¬ IsPerfect G := by
  intro h
  obtain ⟨c, hlt, hc⟩ := h {0, 3, 6, 1, 4}
  rw [cliqueNum_C5] at hlt
  let c' : Fin 7 → Fin 2 := fun v => if c v = 0 then 0 else 1
  obtain ⟨u, hu, v, hv, huv, he⟩ := C5_not_two_col c'
  have h1 := hlt u hu
  have h2 := hlt v hv
  apply hc u hu v hv huv
  simp only [c'] at he
  split_ifs at he <;> omega

/-- The even hole `1-5-2-6`. -/
def hole4 : Fin 4 → Fin 7 := ![1, 5, 2, 6]

lemma hole4_isHole : IsHole G hole4 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro a b h; revert a b; decide
  · decide

/-- **The Automated Conjecturing III conjecture
`(((is_circular_planar) -> (is_perfect)) -> (is_clique)) -> (is_even_hole_free)` is false.** -/
theorem not_conjecture : ¬ Conjecture := by
  intro h
  have := h (Fin 7) G G_connected (fun hp => absurd (hp G_outerplanar) G_not_perfect)
  exact this 4 hole4 hole4_isHole ⟨2, rfl⟩

end AC3EHF

#print axioms AC3EHF.not_conjecture
