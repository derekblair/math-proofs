import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace PetersenSharp

abbrev B := Fin 10
abbrev D := ZMod 5
abbrev V := B × D
abbrev P := Fin 3

def base (u : B) (p : P) : B :=
  if hu : u.val < 5 then
    if p=0 then ⟨(u.val+1)%5,by omega⟩
    else if p=1 then ⟨(u.val+4)%5,by omega⟩
    else ⟨u.val+5,by omega⟩
  else
    if p=0 then ⟨5+(u.val+2)%5,by omega⟩
    else if p=1 then ⟨5+(u.val+3)%5,by omega⟩
    else ⟨u.val-5,by omega⟩

def gain (u v : B) : D :=
  if (u,v)=(3,8) then 1 else
  if (u,v)=(6,8) then 2 else
  if (u,v)=(6,9) then 3 else
  if (u,v)=(7,9) then 4 else 0

def volt (u v : B) : D := gain u v - gain v u

def next (u : V) (p : P) : V :=
  let v := base u.1 p
  (v,u.2+volt u.1 v)

def rev (p : P) : P := ![1,0,2] p

def edge (u v : V) : Prop := ∃ p : P, next u p = v

instance (u v : V) : Decidable (edge u v) := by unfold edge; infer_instance

theorem base_back (u : B) (p : P) : base (base u p) (rev p) = u := by decide +revert

theorem back (u : V) (p : P) : next (next u p) (rev p) = u := by
  rcases u with ⟨b,d⟩
  unfold next
  simp only [base_back]
  congr 1
  unfold volt
  abel

theorem edge_symm {u v : V} (e : edge u v) : edge v u := by
  obtain ⟨p,rfl⟩ := e
  exact ⟨rev p,back u p⟩

theorem no_loop (u : V) : ¬ edge u u := by decide +revert


theorem next_inj (u : V) : Function.Injective (next u) := by decide +revert

/-- Exactly three neighbors, exposed by the three distinct lift ports. -/
noncomputable def neighbors (u : V) : Equiv P {v : V // edge u v} :=
  Equiv.ofBijective (fun p => ⟨next u p,p,rfl⟩) ⟨
    fun _ _ e => next_inj u (congrArg Subtype.val e),
    fun ⟨_v,p,e⟩ => ⟨p,Subtype.ext e⟩⟩

def shift (d : D) (u : V) : V := (u.1,u.2+d)

theorem shift_next (d : D) (u : V) (p : P) :
    shift d (next u p) = next (shift d u) p := by
  rcases u with ⟨b,z⟩
  simp [shift,next,add_assoc,add_comm]

theorem shift_inj (d : D) : Function.Injective (shift d) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ h
  have e : u=v := congrArg (Prod.fst : V → B) h
  have k : a+d=b+d := congrArg (Prod.snd : V → D) h
  exact Prod.ext e (add_right_cancel k)

end PetersenSharp
