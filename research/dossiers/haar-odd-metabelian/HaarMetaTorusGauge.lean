import HaarMetaTorusVoltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarMetaTorusGauge
open HaarMetaTorusVoltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  ![0,0 + W 0 10 - W 1 10,0 + W 0 9 - W 2 9,0 + W 0 12 - W 3 12,0 + W 0 10 - W 1 10 + W 1 13 - W 4 13,0 + W 0 12 - W 5 12,0 + W 0 9 - W 6 9,0 + W 0 10 - W 7 10,0 + W 0 10 - W 1 10 + W 1 11 - W 8 11,0 + W 0 9,0 + W 0 10,0 + W 0 10 - W 1 10 + W 1 11,0 + W 0 12,0 + W 0 10 - W 1 10 + W 1 13,0 + W 0 9 - W 2 9 + W 2 14,0 + W 0 12 - W 3 12 + W 3 15,0 + W 0 10 - W 1 10 + W 1 13 - W 4 13 + W 4 16,0 + W 0 12 - W 5 12 + W 5 17]

def weights (W : B → B → A) : Fin 10 → A :=
  ![W 2 11 + potential W 2 - potential W 11,W 3 13 + potential W 3 - potential W 13,W 4 14 + potential W 4 - potential W 14,W 5 14 + potential W 5 - potential W 14,W 6 15 + potential W 6 - potential W 15,W 6 16 + potential W 6 - potential W 16,W 7 16 + potential W 7 - potential W 16,W 7 17 + potential W 7 - potential W 17,W 8 15 + potential W 8 - potential W 15,W 8 17 + potential W 8 - potential W 17]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 10, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j <;>
  simp [map,Fin.sum_univ_succ,gauge,next,weights,potential] <;>
  (try simp only [anti 0 9,anti 0 10,anti 0 12,anti 1 10,anti 1 11,anti 1 13,anti 2 9,anti 2 11,anti 2 14,anti 3 12,anti 3 13,anti 3 15,anti 4 13,anti 4 14,anti 4 16,anti 5 12,anti 5 14,anti 5 17,anti 6 9,anti 6 15,anti 6 16,anti 7 10,anti 7 16,anti 7 17,anti 8 11,anti 8 15,anti 8 17]) <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarMetaTorusVoltage.HasCycle (map W) n) : HasCycle W n := by
  obtain ⟨v,inj,cv⟩ := C
  let f (s : B × A) : B × A := (s.1,s.2 + potential W s.1)
  have fi : Function.Injective f := by
    rintro ⟨u,a⟩ ⟨v,b⟩ e
    have g : u=v := congrArg (fun k : B × A => k.1) e
    subst v
    have h : a + potential W u = b + potential W u := congrArg (fun k : B × A => k.2) e
    exact congrArg (Prod.mk u) (add_right_cancel h)
  refine ⟨f ∘ v,fi.comp inj,?_⟩
  intro i
  let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  obtain ⟨k,hk,e⟩ := cv i
  have m := map_gauge W anti (v i).1 k
  rw [hk] at m
  change (v i).2 + map W (gauge (v i).1 (v j).1) = (v j).2 at e
  rw [m] at e
  refine ⟨k,hk,?_⟩
  change (v i).2+potential W (v i).1+W (v i).1 (v j).1 = (v j).2+potential W (v j).1
  rw [← e]
  abel

end HaarMetaTorusGauge
