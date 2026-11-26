import RibbonClass4Ports
import HaarClass3Separation64

namespace RibbonClass4Short

open HaarClass4Table HaarClass4Normal HaarClass4Projection HaarClass4Ports HaarClass4Structure
open RibbonClass4Data (suitable leftX leftY cancelX cancelY)
variable {G H : Type*} [Group G] [Group H]

def word : Fin 32 → Fin 3 :=
  ![1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1]

abbrev State := Bool × Row

def next (s : State) (p : Fin 3) : State :=
  if p=2 then (!s.1,s.2)
  else (s.1, if s.1 then (if p=0 then rightY s.2 else leftY s.2)
             else (if p=0 then rightX s.2 else leftX s.2))

def trace : Nat → State
  | 0 => (false,base)
  | n+1 => next (trace n) (word ⟨n%32,Nat.mod_lt _ (by decide)⟩)

private theorem closed : trace 32=trace 0 := by decide +kernel
private theorem ranged : ∀ i : Fin 32, suitable (trace i.val).2.i := by decide +kernel

def small4 (d : ℤ) : Prop := d=1 ∨ d= -1 ∨ d=2 ∨ d= -2 ∨ d=4 ∨ d= -4
instance (d : ℤ) : Decidable (small4 d) := by unfold small4; infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem sep : ∀ i j : Fin 32, i≠j → (trace i.val).1=(trace j.val).1 →
    let d := diff (trace i.val).2 (trace j.val).2
    small4 d.i ∨ small4 d.j ∨ (d.i=0 ∧ d.j=0 ∧ small4 d.c) := by decide +kernel

def Good (c : H) : Prop := c^(4:Nat)≠1

private theorem reject (c : H) (h : Good c) (d : ℤ) (ds : small4 d) : c^d≠1 := by
  have h1 : c≠1 := fun h' => h (by simp [h'])
  have h2 : c^2≠1 := fun h' => h (by rw [show (4:Nat)=2*2 from rfl,pow_mul,h',one_pow])
  rcases ds with u|u|u|u|u|u <;> subst d <;> norm_num [zpow_neg] <;> assumption

private def vertex (M : Data G) (s : State) : Bool × G := (s.1,eval M s.2)

private theorem step_adj (M : Data G) (s : State) (p : Fin 3) (R : suitable s.2.i) :
    Ribbon.Adj M.x M.y (vertex M s) (vertex M (next s p)) := by
  obtain ⟨b,r⟩ := s
  have HX : eval M (rightX r)=eval M r*M.x := eval_x M r
  have HY : eval M (rightY r)=eval M r*M.y := eval_y M r R
  have MX := eval_x M (leftX r)
  have MY := eval_y M (leftY r) R
  rw [cancelX] at MX
  rw [cancelY] at MY
  cases b <;> fin_cases p <;> norm_num [Ribbon.Adj,next,vertex]
  · exact Or.inl HX.symm
  · exact Or.inr MX.symm
  · exact Or.inl HY.symm
  · exact Or.inr MY.symm

theorem cycle32 (M : Data G) (φ : G→*H) (k : KillsMid M φ) (good : Good (φ M.c)) :
    Ribbon.Cycle M.x M.y 32 := by
  let f : Fin 32 → Bool × G := fun i => vertex M (trace i.val)
  refine ⟨f,?_,?_⟩
  · intro i j eq
    by_contra neq
    have C := projections_of_equal M φ k (trace i.val).2 (trace j.val).2 (congrArg Prod.snd eq)
    have E := sep i j neq (congrArg (fun u : Bool × G => u.1) eq)
    rcases E with h|h|⟨hi,hj,h⟩
    · exact reject _ good _ h C.1
    · exact reject _ good _ h C.2.1
    · exact reject _ good _ h (C.2.2 hi hj)
  · intro i
    have F : Ribbon.Adj M.x M.y (vertex M (trace i.val)) (vertex M (trace (i.val+1))) :=
      step_adj M _ _ (ranged i)
    change Ribbon.Adj M.x M.y (vertex M (trace i.val)) (vertex M (trace ((i.val+1)%32)))
    by_cases E : i.val+1<32
    · simpa [Nat.mod_eq_of_lt E] using F
    · have H : i.val+1=32 := by omega
      rw [H,Nat.mod_self]
      rwa [H,closed] at F

theorem odd_proj_cycle32 (nil : LS G 4=⊥) (odd : Odd (Nat.card G)) (x y : G)
    (hc : portC x y∉LS G 2) : Ribbon.Cycle x y 32 := by
  let C := RibbonClass4.proj G (portC x y)
  have hn : C≠1 := fun eq => hc ((QuotientGroup.eq_one_iff _).mp eq)
  have o := HaarClass3Separation64.odd_projection odd
  have h2 := HaarClass3Odd.odd_no_involution o hn
  have h4 : C^(4:Nat)≠1 := by
    intro eq
    apply HaarClass3Odd.odd_no_involution o h2
    rwa [←pow_mul]
  exact cycle32 (make nil x y) (RibbonClass4.proj G) (RibbonClass4.kills nil x y) h4

end RibbonClass4Short
#print axioms RibbonClass4Short.odd_proj_cycle32
