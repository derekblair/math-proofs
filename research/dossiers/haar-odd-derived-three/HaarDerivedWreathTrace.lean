import HaarDerivedWreathCore

namespace HaarDerivedWreathTrace
open HaarDerivedWreathCore HaarSharpPortGeometry
variable {Q : Type*} [Group Q] [DecidableEq Q]

def basePort (x y : Q) (c : Fin 3) : Q :=
  if c=0 then 1 else if c=1 then x else y

def liftPort (x y : Q) (c : Fin 3) : W Q :=
  if c=0 then 1 else if c=1 then up false x else up true y

@[simp] theorem map_port (x y : Q) (c : Fin 3) : π (liftPort x y c)=basePort x y c := by
  fin_cases c <;> rfl

@[simp] theorem lift_zero (x y : Q) : liftPort x y 0=1 := rfl

def step (x y : Q) (a : Bool × Q) (c : Fin 3) : Bool × Q :=
  (!a.1,a.2 * oriented (basePort x y) a.1 c)

def topStep (x y : Q) (a : Bool × W Q) (c : Fin 3) : Bool × W Q :=
  (!a.1,a.2 * oriented (liftPort x y) a.1 c)

def proj (a : Bool × W Q) : Bool × Q := (a.1,a.2.pos)

theorem step_proj (x y : Q) (a : Bool × W Q) (c : Fin 3) :
    proj (topStep x y a c)=step x y (proj a) c := by
  apply Prod.ext
  · rfl
  · change π (a.2 * oriented (liftPort x y) a.1 c) = π a.2 * oriented (basePort x y) a.1 c
    rcases a with ⟨p,a⟩
    cases p <;> simp [oriented]

def edgeFlow (x y : Q) (a : Bool × Q) (c : Fin 3) (b : Bool) (r : Q) : ℤ :=
  if c=0 ∨ (c=2) ≠ b then 0
  else if a.1 then if (step x y a c).2=r then -1 else 0
  else if a.2=r then 1 else 0

theorem step_flow (x y : Q) (a : Bool × W Q) (c : Fin 3) (b : Bool) (r : Q) :
    (topStep x y a c).2.lamp b r =
      a.2.lamp b r + (edgeFlow x y (proj a) c b r : ZMod 3) := by
  rcases a with ⟨l,a⟩
  cases l <;> fin_cases c <;> cases b
  all_goals simp [topStep,oriented,edgeFlow,proj,liftPort,basePort,step,positive,negative,atPos]
  all_goals split <;> simp_all [sub_eq_add_neg, eq_comm]

def walkFlow (x y : Q) (a : Bool × Q) (labels : List (Fin 3)) (b : Bool) (r : Q) : ℤ :=
  match labels with
  | [] => 0
  | c::cs => edgeFlow x y a c b r + walkFlow x y (step x y a c) cs b r

theorem walk_flow (x y : Q) (a : Bool × W Q) (labels : List (Fin 3)) (b : Bool) (r : Q) :
    (labels.foldl (topStep x y) a).2.lamp b r =
      a.2.lamp b r + (walkFlow x y (proj a) labels b r : ZMod 3) := by
  induction labels generalizing a with
  | nil => simp [walkFlow]
  | cons c cs ih =>
    rw [List.foldl_cons,ih,step_flow,step_proj,walkFlow,Int.cast_add,add_assoc]

theorem closed_mod_flow (x y : Q) (a : Bool × W Q) (labels : List (Fin 3))
    (closed : labels.foldl (topStep x y) a=a) (b : Bool) (r : Q) :
    (3:ℤ) ∣ walkFlow x y (proj a) labels b r := by
  have hcalc := walk_flow x y a labels b r
  rw [closed] at hcalc
  have zero : (walkFlow x y (proj a) labels b r : ZMod 3)=0 := by
    apply add_left_cancel (a := a.2.lamp b r)
    simpa only [add_zero] using hcalc.symm
  exact (CharP.intCast_eq_zero_iff (ZMod 3) 3 _).mp zero

end HaarDerivedWreathTrace
#print axioms HaarDerivedWreathTrace.closed_mod_flow
