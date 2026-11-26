import WeightedWalk
import Mathlib.Tactic

namespace FiniteBalance
variable {V : Type*} [Fintype V] [DecidableEq V]

def edge (P M : V → V → Prop) (a : V) (k : ℤ) (b : V) : Prop :=
  (k=1 ∧ P a b) ∨ (k= -1 ∧ M a b)

variable (P M : V → V → Prop) [DecidableRel P] [DecidableRel M]

def step (R : Finset (V×V)) : Finset (V×V) :=
  R ∪ Finset.univ.filter (fun e =>
      e.1=e.2
      ∨ (∃ x : V, (e.1,x)∈R ∧ (x,e.2)∈R)
      ∨ (∃ x y : V, P e.1 x ∧ (x,y)∈R ∧ M y e.2)
      ∨ (∃ x y : V, M e.1 x ∧ (x,y)∈R ∧ P y e.2))

def reach : ℕ → Finset (V×V)
  | 0 => ∅
  | n+1 => step P M (reach n)

theorem infl (R : Finset (V×V)) : R ⊆ step P M R := Finset.subset_union_left

theorem sound (n : ℕ) (a b : V) (h : (a,b)∈reach P M n) :
    WeightedWalk.Close (edge P M) a b := by
  induction n generalizing a b with
  | zero => simp [reach] at h
  | succ n ih =>
    simp only [reach, step, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    rcases h with h | eq | ⟨x,h,k⟩ | ⟨x,y,p,h,m⟩ | ⟨x,y,m,h,p⟩
    · exact ih a b h
    · cases eq
      exact .nil a
    · exact .join (ih a x h) (ih x b k)
    · exact .pos (Or.inl ⟨rfl,p⟩) (ih x y h) (Or.inr ⟨rfl,m⟩)
    · exact .neg (Or.inr ⟨rfl,m⟩) (ih x y h) (Or.inl ⟨rfl,p⟩)

theorem stationary_from (n : ℕ)
    (h : reach P M (n+1)=reach P M n) :
    ∀ j, reach P M (n+j+1)=reach P M (n+j) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    exact congrArg (step P M) ih

def budget : ℕ := Fintype.card (V×V)

theorem stationary : reach P M (budget (V:=V)+1)=reach P M (budget (V:=V)) := by
  let N := budget (V:=V)
  change reach P M (N+1)=reach P M N
  by_contra h
  have strict : ∀ i≤N, (reach P M i) ⊂ (reach P M (i+1)) := by
    intro i hi
    have ne : reach P M (i+1) ≠ reach P M i := by
      intro e
      have hh := stationary_from P M i e (N-i)
      have ww : i+(N-i)=N := by omega
      rw [ww] at hh
      exact h hh
    exact Finset.ssubset_iff_subset_ne.mpr ⟨infl P M _, Ne.symm ne⟩
  have bound : ∀ i≤N+1, i≤(reach P M i).card := by
    intro i hi
    induction i with
    | zero => omega
    | succ i ih =>
      have z := Finset.card_lt_card (strict i (by omega))
      have zz := ih (by omega)
      omega
  have bb := bound (N+1) (by omega)
  have bc := Finset.card_le_univ (s := reach P M (N+1))
  change (reach P M (N+1)).card ≤ N at bc
  omega

def accept (a b : V) : Bool := decide ((a,b)∈reach P M (budget (V:=V)))

theorem complete (a b : V) (h : WeightedWalk.Close (edge P M) a b) :
    (a,b)∈reach P M (budget (V:=V)) := by
  let G := reach P M (budget (V:=V))
  have eq : step P M G = G := stationary P M
  have put : ∀ x y : V, (x,y)∈step P M G → (x,y)∈G := by
    intro x y h
    rwa [eq] at h
  change (a,b)∈G
  induction h with
  | nil x =>
    apply put
    simp [step]
  | join h₁ h₂ ih₁ ih₂ =>
    apply put
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    exact Or.inr (Or.inl ⟨_,ih₁,ih₂⟩)
  | @pos x y z w e h f ih =>
    apply put
    have ee : P x y := by simpa [edge] using e
    have ff : M z w := by simpa [edge] using f
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    exact Or.inr (Or.inr (Or.inl ⟨_,_,ee,ih,ff⟩))
  | @neg x y z w e h f ih =>
    apply put
    have ee : M x y := by simpa [edge] using e
    have ff : P z w := by simpa [edge] using f
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    exact Or.inr (Or.inr (Or.inr ⟨_,_,ee,ih,ff⟩))

theorem acceptance_iff (a b : V) :
    accept P M a b = true ↔
      ∃ L, WeightedWalk.Walk (edge P M) a b L ∧ L.sum=0 := by
  have hu : ∀ x k y, edge P M x k y → k=1 ∨ k= -1 := by
    rintro x k y (⟨he,_⟩|⟨he,_⟩) <;> tauto
  rw [WeightedWalk.zero_iff_close _ hu]
  simp only [accept,decide_eq_true_eq]
  exact ⟨sound P M _ a b,complete P M a b⟩

end FiniteBalance

#print axioms FiniteBalance.stationary
#print axioms FiniteBalance.acceptance_iff
