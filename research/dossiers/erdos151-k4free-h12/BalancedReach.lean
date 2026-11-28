import DirectedReach
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem flow_balance (N : V → V → Nat)
    (balance : ∀ v, ∑ w : V, N v w = ∑ w : V, N w v)
    (S T : Finset V) (dis : Disjoint S T) (full : S∪T = Finset.univ) :
    (∑ v ∈ S, ∑ w ∈ T, N v w) = (∑ v ∈ T, ∑ w ∈ S, N v w) := by
  have hb : (∑ v ∈ S, ∑ w : V, N v w) = ∑ v ∈ S, ∑ w : V, N w v :=
    Finset.sum_congr rfl (fun v _ => balance v)
  have hi : (∑ v ∈ S, ∑ w ∈ S, N v w) = ∑ v ∈ S, ∑ w ∈ S, N w v := Finset.sum_comm
  rw [← full] at hb
  simp only [Finset.sum_union dis, Finset.sum_add_distrib] at hb
  have hv : (∑ v ∈ S, ∑ w ∈ T, N w v) = ∑ v ∈ T, ∑ w ∈ S, N v w := Finset.sum_comm
  omega

theorem balanced_paths_to_root (R : V → V → Prop) [DecidableRel R]
    (balance : ∀ v, (∑ w : V, if R v w then (1:Nat) else 0) =
      ∑ w : V, if R w v then (1:Nat) else 0)
    (p : V) (weak : ∀ v, ∃ n, Steps (fun a b => R a b ∨ R b a) n v p) :
    ∀ v, ∃ n, Steps R n v p := by
  classical
  let Q v := ∃ n, Steps R n v p
  let S := Finset.univ.filter Q
  let T := Finset.univ \ S
  have ms (v : V) : v ∈ S ↔ Q v := by simp [S]
  have mt (v : V) : v ∈ T ↔ ¬ Q v := by simp [T,ms]
  have dl : Disjoint S T :=
    Finset.disjoint_left.mpr (fun v hS hT => (mt v).mp hT ((ms v).mp hS))
  have fu : S∪T = Finset.univ := by
    ext v
    by_cases h : Q v <;> simp [ms,mt,h]
  have no (v w : V) (h : R v w) : Q w → Q v := by
    rintro ⟨n,path⟩
    exact ⟨n+1,Steps.more h path⟩
  have rev : (∑ v ∈ T, ∑ w ∈ S, if R v w then (1:Nat) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    exact if_neg (fun h => (mt v).mp hv (no v w h ((ms w).mp hw)))
  have hv := flow_balance (fun v w => if R v w then 1 else 0) balance S T dl fu
  rw [rev] at hv
  have close (v w : V) (h : R w v) (qw : Q w) : Q v := by
    by_contra! qv
    have b1 : 1 ≤ ∑ x ∈ T, if R w x then (1:Nat) else 0 := by
      have b := Finset.single_le_sum (f := fun x => if R w x then (1:Nat) else 0)
        (fun _ _ => Nat.zero_le _) ((mt v).mpr qv)
      simpa [h] using b
    have b2 : (∑ x ∈ T, if R w x then (1:Nat) else 0) ≤
        ∑ y ∈ S, ∑ x ∈ T, if R y x then (1:Nat) else 0 :=
      Finset.single_le_sum (f := fun y => ∑ x ∈ T, if R y x then (1:Nat) else 0)
        (fun _ _ => Nat.zero_le _) ((ms w).mpr qw)
    omega
  have qend : Q p := ⟨0,Steps.zero p⟩
  have aux {n a b} (pth : Steps (fun a b => R a b ∨ R b a) n a b) :
      Q b → Q a := by
    induction pth with
    | zero v => intro h; exact h
    | more h _ ih =>
      intro hb
      rcases h with h|h
      · exact no _ _ h (ih hb)
      · exact close _ _ h (ih hb)
  intro v
  obtain ⟨_,path⟩ := weak v
  exact aux path qend

#print axioms flow_balance
#print axioms balanced_paths_to_root
end Erdős151.H12
