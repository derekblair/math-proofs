import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Graph Brain Project open lower bound #19 on the independence number is true

`math1um/objects-invariants-properties`, issue #421 (7 Sep 2017), 19th of the 89 lower bounds:

> `independence_number(x) >= ceil(card_independence_irreducible_part(x)/szekeres_wilf(x))`

`szekeres_wilf` (gt.sage) is `1 + max_{H ⊆ G} δ(H)` (one plus the degeneracy), and
`card_independence_irreducible_part` is the number of vertices outside the KE part of Larson's
independence decomposition — in particular some subset of `V`. We prove the stronger statement
that `⌈|S| / sw(G)⌉ ≤ α(G)` for **every** vertex set `S` of **every** finite graph (no
connectivity needed), which implies #19 whatever the precise irreducible part is.

Proof: the Szekeres–Wilf greedy argument gives an independent set `I` with
`|V| ≤ sw(G)·|I|` (repeatedly take a vertex of minimum degree in what remains, discard its
neighbourhood); hence `|S| ≤ |V| ≤ sw(G)·α(G)`.
-/

namespace GBP421_019

open SimpleGraph Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Degree of `v` inside `T`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) : ℕ :=
  #(T.filter (G.Adj v))

/-- Degeneracy: maximum over nonempty `T` of the minimum degree of `G[T]`. -/
def degeneracy (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  univ.powerset.sup fun T => if h : T.Nonempty then T.inf' h (degIn G T) else 0

/-- `szekeres_wilf = 1 + degeneracy`. -/
def szekeresWilf (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := 1 + degeneracy G

/-- Strengthened form of GBP #421 lower bound #19 (for every vertex set `S`). -/
def Conjecture19Strong : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (S : Finset W), ⌈(#S : ℝ) / (szekeresWilf G : ℝ)⌉ ≤ (G.indepNum : ℤ)

lemma exists_low (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : T.Nonempty) :
    ∃ v ∈ T, degIn G T v ≤ degeneracy G := by
  obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_inf' hT (degIn G T)
  refine ⟨v, hv, ?_⟩
  have := Finset.le_sup (f := fun T : Finset V => if h : T.Nonempty then T.inf' h (degIn G T) else 0)
    (Finset.mem_powerset.2 (Finset.subset_univ T))
  simp only [hT, dite_true] at this
  unfold degeneracy
  rw [← he]; exact this

/-- Greedy: every `T` contains an independent `I` with `|T| ≤ (d+1)|I|`. -/
lemma greedy (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ n, ∀ T : Finset V, #T = n →
      ∃ I ⊆ T, G.IsIndepSet (I : Set V) ∧ #T ≤ (degeneracy G + 1) * #I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hTn
    rcases T.eq_empty_or_nonempty with rfl | hT
    · exact ⟨∅, by simp, by simp [IsIndepSet], by simp⟩
    obtain ⟨v, hv, hdeg⟩ := exists_low G T hT
    let T' := (T.erase v).filter fun w => ¬ G.Adj v w
    have hT' : T' = (T.erase v).filter fun w => ¬ G.Adj v w := rfl
    have hsplit : #T ≤ #T' + (degIn G T v + 1) := by
      have h1 : #(T.erase v) + 1 = #T := Finset.card_erase_add_one hv
      have h2 : #((T.erase v).filter fun w => G.Adj v w) +
          #((T.erase v).filter fun w => ¬ G.Adj v w) = #(T.erase v) :=
        Finset.card_filter_add_card_filter_not _
      have h3 : #((T.erase v).filter fun w => G.Adj v w) ≤ degIn G T v :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset v T))
      have h4 : #T' = #((T.erase v).filter fun w => ¬ G.Adj v w) := rfl
      omega
    have hlt : #T' < n := by
      have : T' ⊆ T.erase v := Finset.filter_subset _ _
      have := Finset.card_le_card this
      have := Finset.card_erase_lt_of_mem hv
      omega
    obtain ⟨I', hI'T, hI'ind, hI'card⟩ := ih _ hlt T' rfl
    have hvI' : v ∉ I' := fun h => by
      have := hI'T h; simp [hT'] at this
    refine ⟨insert v I', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hv
      · exact Finset.mem_of_mem_erase (Finset.filter_subset _ _ (hI'T hx))
    · rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert]
      refine ⟨(isIndepSet_iff G).1 hI'ind, fun w hw _ => ?_⟩
      have := hI'T hw
      simp only [hT', Finset.mem_filter] at this
      exact ⟨this.2, fun h => this.2 h.symm⟩
    · rw [Finset.card_insert_of_notMem hvI']
      nlinarith

theorem card_le_sw_mul_indepNum (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤ szekeresWilf G * G.indepNum := by
  obtain ⟨I, -, hI, hc⟩ := greedy G _ univ rfl
  have := hI.card_le_indepNum
  rw [card_univ] at hc
  unfold szekeresWilf
  calc Fintype.card V ≤ (degeneracy G + 1) * #I := hc
    _ ≤ (1 + degeneracy G) * G.indepNum := by rw [add_comm]; exact Nat.mul_le_mul_left _ this

/-- **Graph Brain Project lower bound #19 (issue #421) holds, in strengthened form.** -/
theorem conjecture19_strong : Conjecture19Strong := by
  intro W _ _ G _ S
  have h1 := card_le_sw_mul_indepNum G
  have h2 : #S ≤ Fintype.card W := Finset.card_le_univ S
  have hsw : (0 : ℝ) < szekeresWilf G := by unfold szekeresWilf; positivity
  rw [Int.ceil_le, div_le_iff₀ hsw]
  have : (#S : ℝ) ≤ (szekeresWilf G : ℝ) * G.indepNum := by exact_mod_cast h2.trans h1
  push_cast; linarith

end GBP421_019

#print axioms GBP421_019.conjecture19_strong
