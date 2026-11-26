import RibbonAbelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic

namespace RibbonSharp

@[ext]
structure H where
  x : ZMod 3
  y : ZMod 3
  z : ZMod 3
  deriving DecidableEq

def prod (a b : H) : H := ⟨a.x+b.x,a.y+b.y,a.z+b.z+a.x*b.y⟩
def one : H := ⟨0,0,0⟩
def inverse (a : H) : H := ⟨-a.x,-a.y,-a.z+a.x*a.y⟩
instance : Group H where
  mul := prod
  one := one
  inv := inverse
  mul_assoc a b c := by change prod (prod a b) c = prod a (prod b c); ext <;> simp [prod] <;> ring
  one_mul a := by change prod one a=a; ext <;> simp [prod,one]
  mul_one a := by change prod a one=a; ext <;> simp [prod,one]
  inv_mul_cancel a := by change prod (inverse a) a=one; ext <;> simp [prod,inverse,one]

def a : H := ⟨1,0,0⟩
def b : H := ⟨0,1,0⟩
def c : H := ⟨0,0,1⟩
theorem ca : Commute c a := by change c*a=a*c; decide +kernel
theorem cb : Commute c b := by change c*b=b*c; decide +kernel
theorem rel : a*b=b*a*c := by decide +kernel
theorem cycle16 : Ribbon.Cycle a b 16 :=
  Ribbon.cycle16 a b c ca cb rel (by decide +kernel) (by decide +kernel)

abbrev V := Bool × H
abbrev P := Fin 3
def step (s : V) (j : P) : V :=
  if j=2 then (!s.1,s.2) else
    (s.1,s.2*(if s.1 then (if j=0 then b else b⁻¹) else (if j=0 then a else a⁻¹)))

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

def left (g : H) (v : V) : V := (v.1,g*v.2)
theorem left_inj (g : H) : Function.Injective (left g) := by
  intro u v e
  have h := congrArg Prod.fst e
  have h' := congrArg Prod.snd e
  exact Prod.ext h (mul_left_cancel h')
theorem left_step (g : H) (v : V) (j : P) : left g (step v j)=step (left g v) j := by
  unfold step left
  split <;> simp [mul_assoc]

def trace {n : Nat} (hn : 0<n) (u : V) (f : Fin n → P) : Nat → V
  | 0 => u
  | i+1 => step (trace hn u f i) (f ⟨i%n,Nat.mod_lt _ hn⟩)

def good {n : Nat} (hn : 0<n) (s : Bool) (f : Fin n → P) : Prop :=
  trace hn (s,1) f n=(s,1) ∧ Function.Injective (fun i : Fin n => trace hn (s,1) f i.val)
instance {n : Nat} (hn : 0<n) (s : Bool) (f : Fin n → P) : Decidable (good hn s f) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i j, _ → i=j))

theorem cycle_good {n : Nat} (hn : 0<n) (C : Ribbon.Cycle a b n) :
    ∃ s f, good hn s f := by
  obtain ⟨v,vi,ve⟩ := C
  have parts (i : Fin n) := adj_port (ve i)
  choose f hf using parts
  let root := v ⟨0,hn⟩
  let g := root.2⁻¹
  have e (i : Nat) :
      trace hn (root.1,1) f i = left g (v ⟨i%n,Nat.mod_lt _ hn⟩) := by
    induction i with
    | zero => simpa [trace,left,root,g] using inv_mul_cancel root.2
    | succ i ih =>
      rw [trace,ih,←left_step,hf]
      apply congrArg (left g ∘ v)
      apply Fin.ext
      exact Nat.mod_add_mod _ _ _
  refine ⟨root.1,f,?_,?_⟩
  · simp [e,left,root,g]
  · intro i j eq
    apply vi
    apply left_inj g
    simpa [e,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using eq

set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem none4 : ∀ (s : Bool) (f : Fin 4 → P), ¬good (by decide) s f := by decide +kernel
private theorem split8 (s : Bool) (x y : P) :
    ∀ f : Fin 6 → P, ¬good (by decide) s (Fin.cons x (Fin.cons y f)) := by
  cases s <;> fin_cases x <;> fin_cases y <;> decide +kernel

theorem none8 (s : Bool) (f : Fin 8 → P) : ¬good (by decide) s f := by
  have h := split8 s (f 0) (Fin.tail f 0) (Fin.tail (Fin.tail f))
  rw [Fin.cons_self_tail,Fin.cons_self_tail] at h
  exact h

theorem sharp : ¬Ribbon.Cycle a b 4 ∧ ¬Ribbon.Cycle a b 8 ∧ Ribbon.Cycle a b 16 := by
  exact ⟨fun H => let ⟨s,f,g⟩ := cycle_good (by decide) H; none4 s f g,
    fun H => let ⟨s,f,g⟩ := cycle_good (by decide) H; none8 s f g, cycle16⟩

end RibbonSharp
#print axioms RibbonSharp.sharp
