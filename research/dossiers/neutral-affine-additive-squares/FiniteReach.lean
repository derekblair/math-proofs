import Mathlib.Tactic

namespace FiniteReach
variable {V : Type*} (R : V→V→Prop) (target : V)

inductive Path : V → Prop
  | done : Path target
  | more {u v} : R u v → Path v → Path u

variable [Fintype V] [DecidableEq V] [DecidableRel R]

def next (Q : Finset V) : Finset V :=
  Q ∪ Finset.univ.filter (fun u => ∃ v∈Q, R u v)

def seen : ℕ → Finset V
  | 0 => {target}
  | n+1 => next R (seen n)

theorem sound (n : ℕ) (x : V) (h : x∈seen R target n) : Path R target x := by
  induction n generalizing x with
  | zero =>
    have e : x=target := Finset.mem_singleton.mp h
    subst x; exact .done
  | succ n ih =>
    rcases Finset.mem_union.mp h with old|new
    · exact ih x old
    · obtain ⟨v,hv,hr⟩ := (Finset.mem_filter.mp new).2
      exact .more hr (ih _ hv)

theorem stable_from (n : ℕ) (e : seen R target (n+1)=seen R target n) :
    ∀ i, seen R target (n+i+1)=seen R target (n+i) := by
  intro i
  induction i with
  | zero => simpa using e
  | succ i ih => exact congrArg (next R) ih

theorem stationary :
    next R (seen R target (Fintype.card V)) = seen R target (Fintype.card V) := by
  let N := Fintype.card V
  change seen R target (N+1)=seen R target N
  by_contra e
  have growth (i : ℕ) (hi : i ≤ N) : (seen R target i).card < (seen R target (i+1)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_union_left,?_⟩
    intro H
    have q := stable_from R target i H.symm (N-i)
    have y : i+(N-i)=N := by omega
    rw [y] at q
    exact e q
  have larger (i : ℕ) (hi : i ≤ N+1) : i ≤ (seen R target i).card := by
    induction i with
    | zero => omega
    | succ i ih => have g := growth i (by omega); have c := ih (by omega); omega
  have p := larger (N+1) le_rfl
  have q := Finset.card_le_univ (s:=seen R target (N+1))
  change (seen R target (N+1)).card ≤ N at q
  omega

def test (x : V) : Bool := decide (x∈seen R target (Fintype.card V))

theorem completeness (x : V) (h : Path R target x) :
    x∈seen R target (Fintype.card V) := by
  induction h with
  | done =>
    generalize Fintype.card V = n
    induction n with
    | zero => simp [seen]
    | succ n ih => exact Finset.mem_union_left _ ih
  | @more u v e h ih =>
    rw [← stationary R target]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,ih,e⟩)

theorem test_iff (x : V) : test R target x=true ↔ Path R target x := by
  simp only [test,decide_eq_true_eq]
  exact ⟨sound R target _ x,completeness R target x⟩

end FiniteReach
#print axioms FiniteReach.test_iff
