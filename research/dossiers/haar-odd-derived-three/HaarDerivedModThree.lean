import HaarDerivedZeroFlow
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Equiv.Basic

namespace HaarDerivedModThree
open HaarDerivedFlowPositive HaarDerivedZeroFlow
variable {V : Type*} [Fintype V] [DecidableEq V]

def count (a : Nat → V) (N : Nat) (u v : V) : ℤ :=
  ∑ i : Fin N, if a i.val=u ∧ a (i.val+1)=v then 1 else 0

def flow (a : Nat → V) (N : Nat) (u v : V) : ℤ :=
  count a N u v - count a N v u

theorem count_nonneg (a : Nat → V) (N : Nat) (u v : V) : 0≤count a N u v := by
  apply Finset.sum_nonneg
  intro i _
  split <;> decide

theorem count_pos (a : Nat → V) (N : Nat) (u v : V) :
    0<count a N u v ↔ Used a N u v := by
  constructor
  · intro h
    by_contra no
    have X : count a N u v=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬ (a i.val=u ∧ a (i.val+1)=v) := fun H => no ⟨i,H⟩
      simp [hn]
    rw [X] at h
    exact (lt_irrefl 0) h
  · rintro ⟨i,ht⟩
    apply Finset.sum_pos'
    · intro j _
      split <;> decide
    · exact ⟨i,Finset.mem_univ _,by simp [ht]⟩

theorem flow_pos_used (a : Nat → V) (N : Nat) (u v : V) :
    0<flow a N u v → Used a N u v := by
  intro H
  apply (count_pos a N u v).mp
  have r := count_nonneg a N v u
  unfold flow at H
  omega

theorem sum_start (a : Nat → V) (N : Nat) (u : V) :
    (∑ v, count a N u v) = ∑ i : Fin N, if a i.val=u then (1:ℤ) else 0 := by
  classical
  unfold count
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases H : a i.val=u
  · simp [H]
  · simp [H]

theorem sum_finish (a : Nat → V) (N : Nat) (u : V) :
    (∑ v, count a N v u) = ∑ i : Fin N, if a (i.val+1)=u then (1:ℤ) else 0 := by
  classical
  unfold count
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases H : a (i.val+1)=u
  · simp [H]
  · simp [H]

theorem flow_balance (a : Nat → V) (N : Nat) (N0 : 1<N)
    (period : ∀ i, a (i+N)=a i) (u : V) :
    (∑ v, flow a N u v)=0 := by
  unfold flow
  rw [Finset.sum_sub_distrib,sum_start,sum_finish,sub_eq_zero]
  letI : NeZero N := ⟨by omega⟩
  let b : Fin N ≃ Fin N := Equiv.addRight 1
  symm
  apply Fintype.sum_equiv b
  intro i
  have Z : a (i.val+1)=a (b i).val := by
    have X : (b i).val=(i.val+1)%N := by
      change (i+(1:Fin N)).val=_
      rw [Fin.val_add]
      change (i.val+1%N)%N=(i.val+1)%N
      rw [Nat.mod_eq_of_lt N0]
    rw [X,period_mod a N period]
  rw [Z]

theorem count_total (a : Nat → V) (N : Nat) :
    (∑ v : V×V, count a N v.1 v.2) = (N:ℤ) := by
  classical
  rw [Fintype.sum_prod_type]
  simp [sum_start]
  rw [Finset.sum_comm]
  simp

theorem cost_le (a : Nat → V) (N : Nat) : cost (flow a N)≤(N:ℤ) := by
  rw [← count_total a N]
  apply Finset.sum_le_sum
  intro ⟨u,v⟩ _
  have h := count_nonneg a N v u
  change max (count a N u v-count a N v u) 0 ≤ count a N u v
  exact max_le (by omega) (count_nonneg a N _ _)

theorem length_bound (a : Nat → V) (N h : Nat) (N0 : 1<N)
    (R : V → V → Prop) (edges : ∀ i, R (a i) (a (i+1)))
    (noLoop : ∀ v, ¬R v v) (symmetric : ∀ {u v}, R u v → R v u)
    (girth : ∀ k, 3≤k → Cyclic R k → 2*h≤k)
    (period : ∀ i, a (i+N)=a i)
    (noBounce : ∀ i, a (i+2)≠a i)
    (div : ∀ u v, (3:ℤ) ∣ flow a N u v) :
    3*(2*h)≤N := by
  classical
  by_cases nz : ∃ u v, flow a N u v≠0
  · exact nonzero_bound (flow a N) 3 N (2*h) (by decide)
      (fun u v => by simp [flow,neg_sub]) (flow_balance a N N0 period) div nz (cost_le a N)
      (fun k k3 C => by
        apply girth k k3
        obtain ⟨w,h,adj⟩ := C
        refine ⟨w,h,fun i => ?_⟩
        obtain ⟨j,e,f⟩ := flow_pos_used a N _ _ (adj i)
        simpa only [e,f] using edges j.val)
  · have zero (u v : V) : flow a N u v=0 := by by_contra H; exact nz ⟨u,v,H⟩
    have reverse {u v : V} (H : Used a N u v) : Used a N v u := by
      apply (count_pos a N _ _).mp
      have c := (count_pos a N _ _).mpr H
      have d := zero u v
      unfold flow at d
      omega
    have L := zero_bound a N h (by omega) R edges noLoop symmetric girth period noBounce reverse
    omega

end HaarDerivedModThree
#print axioms HaarDerivedModThree.length_bound
