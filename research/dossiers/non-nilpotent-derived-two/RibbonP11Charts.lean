import RibbonStationaryChart
import Mathlib.Data.ZMod.Basic
namespace RibbonP11Charts
open RibbonStationaryWord RibbonStationaryChart Ribbon5Bridge
variable {R G : Type*} [CommRing R] [Group G]

abbrev Flat (R : Type*) := Bool × R × R

def flatStep (a ai b bi tx ty : R) (Q : Flat R) (p : P) : Flat R :=
  let (s,q,t) := Q
  if p=2 then (!s,q,t)
  else if s then
    if p=0 then (s,q*b,t+q*ty) else (s,q*bi,t-(q*bi)*ty)
  else
    if p=0 then (s,q*a,t+q*tx) else (s,q*ai,t-(q*ai)*tx)

theorem flatStep_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (z : Bool×G) (p : P) :
    let f : Bool×G → Flat R := fun (s,g) => (s,μ g,τ g)
    f (action x y z p) = flatStep (R := R) (μ x) (↑(μ x)⁻¹) (μ y) (↑(μ y)⁻¹) (τ x) (τ y) (f z) p := by
  obtain ⟨s,g⟩ := z
  cases s <;> fin_cases p <;> simp [flatStep,action,map_mul,map_inv,H.2,inv_sound μ τ H,
    sub_eq_add_neg,mul_assoc]

theorem flatFold_sound (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (w : List P) (z : Bool×G) :
    let f : Bool×G → Flat R := fun (s,g) => (s,μ g,τ g)
    f (run x y z w) = w.foldl
      (flatStep (R := R) (μ x) (↑(μ x)⁻¹) (μ y) (↑(μ y)⁻¹) (τ x) (τ y)) (f z) := by
  induction w generalizing z with
  | nil => rfl
  | cons p ps ih =>
    change _ = ps.foldl _ _
    rw [show run x y z (p::ps) = run x y (action x y z p) ps by rfl]
    rw [ih,flatStep_sound μ τ H x y z p]

def flatPosition (a ai b bi tx ty : R) (s : Spec) (i : Nat) : Flat R :=
  (s.T.take i).foldl (flatStep a ai b bi tx ty) (false,1,0)

theorem flatPosition_same (μ : G →* Rˣ) (τ : G → R) (H : Aff μ τ)
    (x y : G) (s : Spec) (i j : Nat)
    (eq : pathAt x y s.T.toArray i = pathAt x y s.T.toArray j) :
    flatPosition (R := R) (μ x) (↑(μ x)⁻¹) (μ y) (↑(μ y)⁻¹) (τ x) (τ y) s i =
    flatPosition (R := R) (μ x) (↑(μ x)⁻¹) (μ y) (↑(μ y)⁻¹) (τ x) (τ y) s j := by
  have snd (k : Nat) :
      let d := pathAt x y s.T.toArray k
      (d.1,(μ d.2 : R),τ d.2) =
        flatPosition (R := R) (μ x) (↑(μ x)⁻¹) (μ y) (↑(μ y)⁻¹) (τ x) (τ y) s k := by
    simpa only [pathAt,start,flatPosition,map_one,H.1,Units.val_one] using
      flatFold_sound μ τ H x y (s.T.take k) (false,1)
  rw [←snd i,←snd j,eq]

end RibbonP11Charts
#print axioms RibbonP11Charts.flatPosition_same
