import HomologyThree
import HaarOrbitC7Voltage
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.IntervalCases

namespace HeawoodGirthSix
open HaarOrbitC7Voltage (B P next)
open HaarDerivedFlowPositive HaarDerivedCoverTransfer

def Edge (u v : B) : Prop := ∃ p : P, next u p=v
instance (u v : B) : Decidable (Edge u v) := inferInstanceAs (Decidable (∃ p : P, _))

theorem back : ∀ (u : B) (p : P), next (next u p) p=u := by decide +kernel
theorem no_loop : ∀ u : B, ¬ Edge u u := by decide +kernel
theorem symm {u v : B} (e : Edge u v) : Edge v u := by
  obtain ⟨p,h⟩ := e
  exact ⟨p,h ▸ back u p⟩

def orb {n : ℕ} (hn : 0<n) (u : B) (f : Fin n→P) : ℕ → B
  | 0 => u
  | i+1 => next (orb hn u f i) (f ⟨i%n,Nat.mod_lt _ hn⟩)

def Good {n : ℕ} (hn : 0<n) (u : B) (f : Fin n→P) : Prop :=
  orb hn u f n=u ∧ Function.Injective (fun i : Fin n => orb hn u f i.val)
instance {n : ℕ} (hn : 0<n) (u : B) (f : Fin n→P) : Decidable (Good hn u f) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i j, _ → i=j))

theorem to_good {n : ℕ} (hn : 0<n) (C : Cyclic Edge n) :
    ∃ u f, Good hn u f := by
  obtain ⟨v,vi,ve⟩ := C
  choose f hf using ve
  have e (i : ℕ) : orb hn (v ⟨0,hn⟩) f i=periodicLift n hn v i := by
    induction i with
    | zero => simp [orb,periodicLift]
    | succ i ih =>
      rw [orb,ih]
      have H := hf ⟨i%n,Nat.mod_lt _ hn⟩
      have idx : (⟨(i%n+1)%n, Nat.mod_lt _ hn⟩ : Fin n)=⟨(i+1)%n,Nat.mod_lt _ hn⟩ :=
        Fin.ext (Nat.mod_add_mod _ _ _)
      rw [idx] at H
      exact H
  refine ⟨v ⟨0,hn⟩,f,?_,?_⟩
  · simp [e,periodicLift]
  · intro i j v_eq
    apply vi
    simpa [e,periodicLift,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using v_eq

set_option maxRecDepth 50000
set_option maxHeartbeats 0
theorem no3 : ∀ (u : B) (f : Fin 3→P), ¬ Good (by decide) u f := by decide +kernel
theorem no4 : ∀ (u : B) (f : Fin 4→P), ¬ Good (by decide) u f := by decide +kernel
theorem no5 : ∀ (u : B) (f : Fin 5→P), ¬ Good (by decide) u f := by decide +kernel

theorem lower (n : ℕ) (hn : 3≤n) (C : Cyclic Edge n) : 6≤n := by
  by_contra! H
  obtain ⟨u,f,g⟩ := to_good (by omega) C
  interval_cases n
  · exact no3 u f g
  · exact no4 u f g
  · exact no5 u f g

end HeawoodGirthSix
#print axioms HeawoodGirthSix.lower
