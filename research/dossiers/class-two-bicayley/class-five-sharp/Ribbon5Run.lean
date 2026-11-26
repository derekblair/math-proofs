import Ribbon5Packed
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace Ribbon5Packed
abbrev P := Fin 3

inductive Runs : Nat → State → P → State → P → Prop where
  | nil (s : State) (p : P) : Runs 0 s p s p
  | cons {n : Nat} {s t : State} {p q r : P}
      (allowed : q ≠ back p) (next : Runs n (step s q) q t r) : Runs (n+1) s p t r

theorem Runs.member {n : Nat} {s t : State} {p q : P} (h : Runs n s p t q) :
    key t ∈ ends n s p := by
  induction h with
  | nil => simp [ends]
  | @cons n s t p q r allowed h ih =>
    unfold ends
    apply List.mem_flatMap.mpr
    refine ⟨q,?_,by simpa [allowed] using ih⟩
    have H : ∀ p : P, p ∈ ([0,1,2] : List P) := by decide
    exact H q

theorem Runs.concat {n m : Nat} {s t u : State} {p q r : P}
    (h : Runs n s p t q) (k : Runs m t q u r) : Runs (n+m) s p u r := by
  induction h with
  | nil => simpa using k
  | @cons n s t p q r allowed h ih =>
    rw [Nat.succ_add]
    exact .cons allowed (ih k)

private theorem choose (p q : P) : ∃ r : P, r≠back p ∧ r≠back q := by
  revert p q
  decide +kernel

theorem compatible (n : Nat) (s : State) (p q : P) :
    ∃ t r r', Runs n s p t r ∧ Runs n s q t r' := by
  induction n generalizing s p q with
  | zero => exact ⟨s,p,q,.nil s p,.nil s q⟩
  | succ n ih =>
    obtain ⟨j,A,B⟩ := choose p q
    obtain ⟨t,r,r',H,K⟩ := ih (step s j) j j
    exact ⟨t,r,r',.cons A H,.cons B K⟩

theorem runs_of_path (v : Nat → State) (i m : Nat) (p : P)
    (edge : ∀ j, i ≤ j → j < i + m → ∃ q, step (v j) q=v (j+1))
    (prev : ∀ j, i ≤ j → j + 1 < i + m →
      ∀ r, step (v j) r=v (j+1) → step (v (j+1)) (back r) ≠ v (j+2))
    (prior : m≠0 → step (v i) (back p) ≠ v (i+1)) :
    ∃ q, Runs m (v i) p (v (i+m)) q := by
  induction m generalizing i p with
  | zero => exact ⟨p,by simpa using Runs.nil (v i) p⟩
  | succ m ih =>
    obtain ⟨q,hq⟩ := edge i le_rfl (by omega)
    have allowed : q≠back p := by
      intro e
      exact prior (by omega) (e ▸ hq)
    obtain ⟨r,h⟩ := ih (i+1) q (by intro j a b; exact edge j (by omega) (by omega))
      (by intro j a b; exact prev j (by omega) (by omega))
      (by intro nz; exact prev i le_rfl (by omega) q hq)
    have w : i+1+m=i+(m+1) := by omega
    rw [w,←hq] at h
    exact ⟨r,.cons allowed h⟩

end Ribbon5Packed
#print axioms Ribbon5Packed.compatible
