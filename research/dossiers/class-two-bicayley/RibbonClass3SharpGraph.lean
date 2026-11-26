import RibbonClass3
import Mathlib.Data.ZMod.Basic

namespace RibbonClass3SharpGraph
open scoped commutatorElement

@[ext]
structure H where
  x : ZMod 11
  y : ZMod 11
  z : ZMod 11
  u : ZMod 11
  v : ZMod 11
  w : ZMod 11
  deriving DecidableEq

def prod (a b : H) : H := ⟨a.x+b.x,a.y+b.y,a.z+b.z,
  a.u+b.u+a.x*b.y,a.v+b.v+a.y*b.z,a.w+b.w+a.x*b.v+a.u*b.z⟩
def one : H := ⟨0,0,0,0,0,0⟩
def inverse (a : H) : H := ⟨-a.x,-a.y,-a.z,-a.u+a.x*a.y,-a.v+a.y*a.z,
  -a.w+a.x*a.v+a.u*a.z-a.x*a.y*a.z⟩

instance : Group H where
  mul := prod
  one := one
  inv := inverse
  mul_assoc a b c := by change prod (prod a b) c = prod a (prod b c); ext <;> simp [prod] <;> ring
  one_mul a := by change prod one a=a; ext <;> simp [prod,one]
  mul_one a := by change prod a one=a; ext <;> simp [prod,one]
  inv_mul_cancel a := by change prod (inverse a) a=one; ext <;> simp [prod,inverse,one] <;> ring

def a : H := ⟨1,0,1,0,0,0⟩
def b : H := ⟨0,1,1,0,0,0⟩

abbrev V := Bool × H
abbrev P := Fin 3
def step (s : V) (j : P) : V :=
  if j=2 then (!s.1,s.2) else
    (s.1,s.2*(if s.1 then (if j=0 then b else b⁻¹) else (if j=0 then a else a⁻¹)))

def back (j : P) : P := ![1,0,2] j

theorem back_step (u : V) (j : P) : step (step u j) (back j)=u := by
  obtain ⟨s,g⟩ := u
  cases s <;> fin_cases j <;> simp [step,back,mul_assoc]

theorem adj_port {u v : V} (e : Ribbon.Adj a b u v) : ∃ j, step u j=v := by
  rcases e with ⟨hu,hv,(h|h)⟩ | ⟨hu,hv,(h|h)⟩ | ⟨s,g⟩
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [step,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [step,hu,mul_assoc] using congrArg (·*a⁻¹) h.symm
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [step,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [step,hu,mul_assoc] using congrArg (·*b⁻¹) h.symm
  · have E : (!u.1)=v.1 := by cases hu : u.1 <;> cases hv : v.1 <;> simp_all
    exact ⟨2,Prod.ext E g⟩

theorem symm {u v : V} (E : Ribbon.Adj a b u v) : Ribbon.Adj a b v u := by
  rcases E with ⟨p,q,h⟩ | ⟨p,q,h⟩ | ⟨p,q⟩
  · exact Or.inl ⟨q,p,h.symm⟩
  · exact Or.inr (Or.inl ⟨q,p,h.symm⟩)
  · exact Or.inr (Or.inr ⟨Ne.symm p,q.symm⟩)

def left (g : H) (v : V) : V := (v.1,g*v.2)

theorem left_inj (g : H) : Function.Injective (left g) := by
  intro u v e
  have h := congrArg Prod.fst e
  have h' := congrArg Prod.snd e
  exact Prod.ext h (mul_left_cancel h')

theorem left_step (g : H) (v : V) (j : P) : left g (step v j)=step (left g v) j := by
  unfold step left
  split <;> simp [mul_assoc]

def ends : Nat → V → P → List V
  | 0, u, _ => [u]
  | n+1, u, p => ([0,1,2] : List P).flatMap fun q =>
    if q=back p then [] else ends n (step u q) q

theorem ends_mem (v : Nat → V) (i m : Nat) (p : P)
    (edge : ∀ j, i ≤ j → j < i + m → ∃ q, step (v j) q=v (j+1))
    (nobounce : ∀ j, i ≤ j → j + 1 < i + m → v j≠v (j+2))
    (prior : m≠0 → step (v i) (back p) ≠ v (i+1)) :
    v (i+m) ∈ ends m (v i) p := by
  induction m generalizing i p with
  | zero => simp [ends]
  | succ m ih =>
    obtain ⟨q,hq⟩ := edge i le_rfl (by omega)
    have allow : q≠back p := by
      intro h
      exact prior (by omega) (h ▸ hq)
    have nofirst (hm : m≠0) : step (v (i+1)) (back q) ≠ v (i+1+1) := by
      rw [←hq,back_step]
      exact nobounce i le_rfl (by omega)
    have h := ih (i+1) q (by intro j hj hj'; exact edge j (by omega) (by omega))
        (by intro j hj hj'; exact nobounce j (by omega) (by omega)) nofirst
    have e : i+1+m=i+(m+1) := by omega
    rw [e,←hq] at h
    unfold ends
    apply List.mem_flatMap.mpr
    refine ⟨q, ?_, by simpa [allow] using h⟩
    fin_cases q <;> decide

def Checked (h : Nat) : Prop :=
  ∀ (s : Bool) (q r : P), q≠r →
    List.Disjoint (ends (h-1) (step (s,1) q) q) (ends (h-1) (step (s,1) r) r)

instance checkedDec (h : Nat) : Decidable (Checked h) :=
  by
    unfold Checked
    have inst (s t : List V) : Decidable (s.Disjoint t) :=
      decidable_of_iff (∀ x ∈ s, ∀ y ∈ t, x ≠ y) List.disjoint_iff_ne.symm
    exact inferInstance

end RibbonClass3SharpGraph
