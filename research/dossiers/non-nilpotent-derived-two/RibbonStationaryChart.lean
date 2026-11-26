import RibbonStationaryWordGraph

namespace RibbonStationaryChart
open Ribbon5Bridge RibbonStationaryWord
variable {R G : Type*} [CommRing R] [Group G]
abbrev State (R : Type*) [CommRing R] := Bool × Rˣ × R

def Aff (μ : G →* Rˣ) (τ : G → R) : Prop :=
  τ 1=0 ∧ ∀ a b, τ (a*b)=τ a+(μ a:R)*τ b

def step (a b : Rˣ) (Q : State R) (p : P) : State R :=
  let (s,q,t) := Q
  if p=2 then (!s,q,t)
  else if s then
    if p=0 then (s,q*b,t+(q:R)) else (s,q*b⁻¹,t-(↑(q*b⁻¹):R))
  else if p=0 then (s,q*a,t) else (s,q*a⁻¹,t)

def position (a b : Rˣ) (s : Spec) (i : Nat) : State R :=
  (s.T.take i).foldl (step a b) (false,1,0)

theorem inv_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ) (g : G) :
    τ g⁻¹ = -(↑((μ g)⁻¹):R)*τ g := by
  have h := H.2 g⁻¹ g
  rw [inv_mul_cancel,H.1,map_inv] at h
  linear_combination -h

theorem step_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (sg : Bool×G) (p : P) :
    let f : Bool×G → State R := fun (s,g) => (s,μ g,τ g)
    f (action x y sg p) = step (μ x) (μ y) (f sg) p := by
  obtain ⟨s,g⟩ := sg
  cases s <;> fin_cases p <;> simp [step,action,map_mul,map_inv,H.2,inv_sound μ τ H,tx,ty,sub_eq_add_neg]

theorem fold_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (w : List P) (sg : Bool×G) :
    let f : Bool×G → State R := fun (s,g) => (s,μ g,τ g)
    f (run x y sg w) = w.foldl (step (μ x) (μ y)) (f sg) := by
  induction w generalizing sg with
  | nil => rfl
  | cons p ps ih =>
    change _ = ps.foldl (step (μ x) (μ y)) _
    rw [show run x y sg (p::ps) = run x y (action x y sg p) ps by rfl]
    rw [ih,step_sound μ τ H x y tx ty]

theorem position_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (s : Spec) (i : Nat) :
    let d := pathAt x y s.T.toArray i
    (d.1,μ d.2,τ d.2) = position (μ x) (μ y) s i := by
  simpa only [pathAt,start,position,map_one,H.1] using
    fold_sound μ τ H x y tx ty (s.T.take i) (false,1)

theorem same (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (s : Spec) (i j : Nat)
    (eq : pathAt x y s.T.toArray i = pathAt x y s.T.toArray j) :
    position (μ x) (μ y) s i = position (μ x) (μ y) s j := by
  rw [←position_sound μ τ H x y tx ty s i,←position_sound μ τ H x y tx ty s j,eq]

end RibbonStationaryChart
#print axioms RibbonStationaryChart.same
