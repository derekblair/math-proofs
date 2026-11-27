import HaarOrbitCylinderVoltage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.OrderOfElement

namespace HaarOrbitCylinderGauge
open HaarOrbitCylinderVoltage
variable {A : Type*} [AddCommGroup A]

def potential (W : B → B → A) : B → A :=
  let p0 : A := 0
  let p18 := p0 + W 0 18
  let p21 := p0 + W 0 21
  let p25 := p0 + W 0 25
  let p3 := p21 - W 3 21
  let p4 := p25 - W 4 25
  let p7 := p25 - W 7 25
  let p24 := p3 + W 3 24
  let p28 := p3 + W 3 28
  let p22 := p4 + W 4 22
  let p29 := p4 + W 4 29
  let p32 := p7 + W 7 32
  let p2 := p24 - W 2 24
  let p6 := p24 - W 6 24
  let p10 := p28 - W 10 28
  let p1 := p22 - W 1 22
  let p11 := p29 - W 11 29
  let p14 := p32 - W 14 32
  let p20 := p2 + W 2 20
  let p23 := p2 + W 2 23
  let p31 := p6 + W 6 31
  let p35 := p10 + W 10 35
  let p19 := p1 + W 1 19
  let p26 := p1 + W 1 26
  let p33 := p11 + W 11 33
  let p5 := p23 - W 5 23
  let p13 := p31 - W 13 31
  let p17 := p35 - W 17 35
  let p8 := p26 - W 8 26
  let p15 := p33 - W 15 33
  let p27 := p5 + W 5 27
  let p30 := p8 + W 8 30
  let p9 := p27 - W 9 27
  let p12 := p30 - W 12 30
  let p34 := p9 + W 9 34
  let p16 := p34 - W 16 34
  ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35]

def weights (W : B → B → A) : Fin 10 → A :=
  ![W 5 26 + potential W 5 - potential W 26,
   W 6 27 + potential W 6 - potential W 27,
   W 7 28 + potential W 7 - potential W 28,
   W 8 29 + potential W 8 - potential W 29,
   W 9 30 + potential W 9 - potential W 30,
   W 10 31 + potential W 10 - potential W 31,
   W 11 32 + potential W 11 - potential W 32,
   W 12 33 + potential W 12 - potential W 33,
   W 13 34 + potential W 13 - potential W 34,
   W 14 35 + potential W 14 - potential W 35]

def map (W : B → B → A) : V →+ A where
  toFun q := ∑ k : Fin 10, q k • weights W k
  map_zero' := by simp
  map_add' q r := by simp [add_zsmul,Finset.sum_add_distrib]

def clean (W : B → B → A) (u v : B) : A := if u=v then 0 else W u v

set_option maxHeartbeats 0 in
theorem map_gauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (u : B) (j : P) :
    map W (gauge u (next u j)) = clean W u (next u j) + potential W u - potential W (next u j) := by
  fin_cases u <;> fin_cases j <;>
  simp [map,Fin.sum_univ_succ,gauge,next,weights,potential,clean] <;>
  (try simp only [anti 0 18, anti 0 21, anti 0 25, anti 1 19, anti 1 22, anti 1 26, anti 2 20, anti 2 23, anti 2 24, anti 3 21, anti 3 24, anti 3 28, anti 4 22, anti 4 25, anti 4 29, anti 5 23, anti 5 26, anti 5 27, anti 6 24, anti 6 27, anti 6 31, anti 7 25, anti 7 28, anti 7 32, anti 8 26, anti 8 29, anti 8 30, anti 9 27, anti 9 30, anti 9 34, anti 10 28, anti 10 31, anti 10 35, anti 11 29, anti 11 32, anti 11 33, anti 12 30, anti 12 33, anti 13 31, anti 13 34, anti 14 32, anti 14 35, anti 15 33, anti 16 34, anti 17 35]) <;> abel

def adj (W : B → B → A) (s t : B × A) : Prop :=
  ∃ j, next s.1 j = t.1 ∧ s.2 + clean W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem ungauge (W : B → B → A) (anti : ∀ u v, W v u = -W u v) {n : Nat}
    (C : HaarOrbitCylinderVoltage.HasCycle (map W) n) : HasCycle W n := by
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

end HaarOrbitCylinderGauge
