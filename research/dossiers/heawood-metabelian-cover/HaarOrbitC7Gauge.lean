import HaarOrbitC7Voltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarOrbitC7Gauge
open HaarOrbitC7Voltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  let p0 : A := 0
  let p7 := p0 + W 0 7
  let p8 := p0 + W 0 8
  let p10 := p0 + W 0 10
  let p4 := p7 - W 4 7
  let p6 := p7 - W 6 7
  let p1 := p8 - W 1 8
  let p5 := p8 - W 5 8
  let p3 := p10 - W 3 10
  let p9 := p1 + W 1 9
  let p11 := p1 + W 1 11
  let p13 := p3 + W 3 13
  let p2 := p9 - W 2 9
  let p12 := p2 + W 2 12
  ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13]

def weights (W : B → B → A) : Fin 8 → A :=
  ![W 2 10 + potential W 2 - potential W 10,
   W 3 11 + potential W 3 - potential W 11,
   W 4 11 + potential W 4 - potential W 11,
   W 4 12 + potential W 4 - potential W 12,
   W 5 12 + potential W 5 - potential W 12,
   W 5 13 + potential W 5 - potential W 13,
   W 6 9 + potential W 6 - potential W 9,
   W 6 13 + potential W 6 - potential W 13]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 8, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

def clean (W : B → B → A) (u v : B) : A := if u=v then 0 else W u v

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = clean W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j <;>
  simp [map,Fin.sum_univ_succ,gauge,next,weights,potential,clean] <;>
  (try simp only [anti 0 7, anti 0 8, anti 0 10, anti 1 8, anti 1 9, anti 1 11, anti 2 9, anti 2 10, anti 2 12, anti 3 10, anti 3 11, anti 3 13, anti 4 7, anti 4 11, anti 4 12, anti 5 8, anti 5 12, anti 5 13, anti 6 7, anti 6 9, anti 6 13]) <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + clean W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarOrbitC7Voltage.HasCycle (map W) n) : HasCycle W n := by
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
  change (v i).2+potential W (v i).1+clean W (v i).1 (v j).1 = (v j).2+potential W (v j).1
  rw [← e]
  abel

end HaarOrbitC7Gauge
