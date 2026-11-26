import HaarOrbitC11Voltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarOrbitC11Gauge
open HaarOrbitC11Voltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  let p0 : A := 0
  let p11 := p0 + W 0 11
  let p12 := p0 + W 0 12
  let p14 := p0 + W 0 14
  let p8 := p11 - W 8 11
  let p10 := p11 - W 10 11
  let p1 := p12 - W 1 12
  let p9 := p12 - W 9 12
  let p3 := p14 - W 3 14
  let p13 := p1 + W 1 13
  let p15 := p1 + W 1 15
  let p17 := p3 + W 3 17
  let p2 := p13 - W 2 13
  let p4 := p15 - W 4 15
  let p6 := p17 - W 6 17
  let p16 := p2 + W 2 16
  let p18 := p4 + W 4 18
  let p20 := p6 + W 6 20
  let p5 := p16 - W 5 16
  let p7 := p18 - W 7 18
  let p19 := p5 + W 5 19
  let p21 := p7 + W 7 21
  ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21]

def weights (W : B → B → A) : Fin 12 → A :=
  ![W 2 14 + potential W 2 - potential W 14,
   W 3 15 + potential W 3 - potential W 15,
   W 4 16 + potential W 4 - potential W 16,
   W 5 17 + potential W 5 - potential W 17,
   W 6 18 + potential W 6 - potential W 18,
   W 7 19 + potential W 7 - potential W 19,
   W 8 19 + potential W 8 - potential W 19,
   W 8 20 + potential W 8 - potential W 20,
   W 9 20 + potential W 9 - potential W 20,
   W 9 21 + potential W 9 - potential W 21,
   W 10 13 + potential W 10 - potential W 13,
   W 10 21 + potential W 10 - potential W 21]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 12, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

def clean (W : B → B → A) (u v : B) : A := if u=v then 0 else W u v

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = clean W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j <;>
  simp [map,Fin.sum_univ_succ,gauge,next,weights,potential,clean] <;>
  (try simp only [anti 0 11, anti 0 12, anti 0 14, anti 1 12, anti 1 13, anti 1 15, anti 2 13, anti 2 14, anti 2 16, anti 3 14, anti 3 15, anti 3 17, anti 4 15, anti 4 16, anti 4 18, anti 5 16, anti 5 17, anti 5 19, anti 6 17, anti 6 18, anti 6 20, anti 7 18, anti 7 19, anti 7 21, anti 8 11, anti 8 19, anti 8 20, anti 9 12, anti 9 20, anti 9 21, anti 10 11, anti 10 13, anti 10 21]) <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + clean W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarOrbitC11Voltage.HasCycle (map W) n) : HasCycle W n := by
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

end HaarOrbitC11Gauge
