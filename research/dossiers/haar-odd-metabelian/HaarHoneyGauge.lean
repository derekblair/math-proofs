import HaarHoneyVoltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarHoneyGauge
open HaarHoneyVoltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  let p0 : A := 0
  let p16 := p0 + W 0 16
  let p17 := p0 + W 0 17
  let p20 := p0 + W 0 20
  let p1 := p17 - W 1 17
  let p4 := p20 - W 4 20
  let p18 := p1 + W 1 18
  let p21 := p1 + W 1 21
  let p24 := p4 + W 4 24
  let p2 := p18 - W 2 18
  let p5 := p21 - W 5 21
  let p8 := p24 - W 8 24
  let p19 := p2 + W 2 19
  let p22 := p2 + W 2 22
  let p25 := p5 + W 5 25
  let p28 := p8 + W 8 28
  let p3 := p19 - W 3 19
  let p6 := p22 - W 6 22
  let p9 := p25 - W 9 25
  let p12 := p28 - W 12 28
  let p23 := p3 + W 3 23
  let p26 := p6 + W 6 26
  let p29 := p9 + W 9 29
  let p7 := p23 - W 7 23
  let p10 := p26 - W 10 26
  let p13 := p29 - W 13 29
  let p27 := p7 + W 7 27
  let p30 := p10 + W 10 30
  let p11 := p27 - W 11 27
  let p14 := p30 - W 14 30
  let p31 := p11 + W 11 31
  let p15 := p31 - W 15 31
  ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31]

def weights (W : B → B → A) : Fin 9 → A :=
  ![W 4 21 + potential W 4 - potential W 21,
   W 5 22 + potential W 5 - potential W 22,
   W 6 23 + potential W 6 - potential W 23,
   W 8 25 + potential W 8 - potential W 25,
   W 9 26 + potential W 9 - potential W 26,
   W 10 27 + potential W 10 - potential W 27,
   W 12 29 + potential W 12 - potential W 29,
   W 13 30 + potential W 13 - potential W 30,
   W 14 31 + potential W 14 - potential W 31]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 9, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

def clean (W : B → B → A) (u v : B) : A := if u=v then 0 else W u v

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = clean W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j <;>
  simp [map,Fin.sum_univ_succ,gauge,next,weights,potential,clean] <;>
  (try simp only [anti 0 16, anti 0 17, anti 0 20, anti 1 17, anti 1 18, anti 1 21, anti 2 18, anti 2 19, anti 2 22, anti 3 19, anti 3 23, anti 4 20, anti 4 21, anti 4 24, anti 5 21, anti 5 22, anti 5 25, anti 6 22, anti 6 23, anti 6 26, anti 7 23, anti 7 27, anti 8 24, anti 8 25, anti 8 28, anti 9 25, anti 9 26, anti 9 29, anti 10 26, anti 10 27, anti 10 30, anti 11 27, anti 11 31, anti 12 28, anti 12 29, anti 13 29, anti 13 30, anti 14 30, anti 14 31, anti 15 31]) <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + clean W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarHoneyVoltage.HasCycle (map W) n) : HasCycle W n := by
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

end HaarHoneyGauge
