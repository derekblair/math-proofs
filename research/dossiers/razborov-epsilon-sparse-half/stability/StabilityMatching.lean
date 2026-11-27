import PetersenArithmetic
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Card
open scoped BigOperators

namespace SparseHalfStability

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Edge := V × V

def OnEdge (v : V) (e : Edge (V := V)) : Prop := v = e.1 ∨ v = e.2
instance (v : V) (e : Edge (V := V)) : Decidable (OnEdge v e) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Ends (M : Finset (Edge (V := V))) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ M, OnEdge v e)

def IsMatching (M : Finset (Edge (V := V))) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, ∀ v, OnEdge v e → OnEdge v f → e = f

def common (B : V → V → Bool) (e : Edge (V := V)) : Finset V :=
  Finset.univ.filter fun v => B e.1 v = true ∧ B e.2 v = true

def exposed (B : V → V → Bool) (M : Finset (Edge (V := V))) (e : Edge (V := V)) :
    Finset V := common B e \ Ends M

def crossMissing (B G : V → V → Bool) (M : Finset (Edge (V := V))) :
    Finset (Edge (V := V)) :=
  Finset.univ.filter fun e => e.1 ∈ Ends M ∧ e.2 ∉ Ends M ∧
    B e.1 e.2 = true ∧ G e.1 e.2 = false

def missingChoice (G : V → V → Bool) (e : Edge (V := V)) (v : V) : V :=
  if G e.1 v then e.2 else e.1

theorem exposed_subtraction (B : V → V → Bool) (M : Finset (Edge (V := V)))
    (e : Edge (V := V)) : (common B e).card ≤ (exposed B M e).card + (Ends M).card := by
  rw [← Finset.card_sdiff_add_card_inter (common B e) (Ends M)]
  apply Nat.add_le_add_left
  exact Finset.card_le_card Finset.inter_subset_right

/-- Each common neighbor of an added matching edge outside the set of
matching endpoints forces a distinct missing edge. The missing edge is
oriented from its unique matching endpoint to the outside vertex. -/
theorem matching_missing (B G : V → V → Bool) (M : Finset (Edge (V := V)))
    (hm : IsMatching M)
    (plus : ∀ e ∈ M, G e.1 e.2 = true)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false) :
    (M.sigma (exposed B M)).card ≤ (crossMissing B G M).card := by
  let pick : Sigma (fun _ : Edge (V := V) => V) → Edge (V := V) :=
    fun z => (missingChoice G z.1 z.2,z.2)
  have endpoint (e : Edge (V := V)) (v : V) : OnEdge (missingChoice G e v) e := by
    unfold missingChoice OnEdge
    split <;> simp
  apply Finset.card_le_card_of_injOn pick
  · intro z hz
    change z ∈ M.sigma (exposed B M) at hz
    obtain ⟨hzM,hzE⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hzC,hzN⟩ := Finset.mem_sdiff.mp hzE
    obtain ⟨ha,hb⟩ := (Finset.mem_filter.mp hzC).2
    change pick z ∈ crossMissing B G M
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,hzN,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.1,hzM,endpoint z.1 z.2⟩
    · change B (missingChoice G z.1 z.2) z.2 = true ∧
        G (missingChoice G z.1 z.2) z.2 = false
      unfold missingChoice
      split
      · exact ⟨hb, tf _ _ _ (plus _ hzM) ‹G z.1.1 z.2 = true›⟩
      · exact ⟨ha, by simpa using ‹¬ G z.1.1 z.2 = true›⟩
  · intro x hx y hy hp
    change x ∈ M.sigma (exposed B M) at hx
    change y ∈ M.sigma (exposed B M) at hy
    have he : missingChoice G x.1 x.2 = missingChoice G y.1 y.2 := congrArg Prod.fst hp
    have he' := endpoint y.1 y.2
    rw [← he] at he'
    have heq := hm x.1 (Finset.mem_sigma.mp hx).1 y.1 (Finset.mem_sigma.mp hy).1
      _ (endpoint x.1 x.2) he'
    cases x
    cases y
    cases heq
    have h := congrArg Prod.snd hp
    cases h
    rfl

#print axioms matching_missing
end SparseHalfStability
