import Ribbon5Family

namespace Ribbon6
open Ribbon5Bridge HaarUniversal36 HaarClass5Commute HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]
def wa : Array P := #[2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1]
def wb : Array P := #[0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2]
def wc : Array P := #[2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1]
def ta : Array Q := #[(false,0,0,0),(true,0,0,0),(true,0,-1,0),(false,0,-1,0),(false,1,-1,0),(false,2,-1,0),(true,2,-1,0),(true,2,-2,-2),(false,2,-2,-2),(false,1,-2,-2),(true,1,-2,-2),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,0,-1),(false,0,0,-1),(false,1,0,-1),(false,2,0,-1),(true,2,0,-1),(true,2,-1,-3),(false,2,-1,-3),(false,1,-1,-3),(true,1,-1,-3),(true,1,-2,-4),(false,1,-2,-4),(false,2,-2,-4),(true,2,-2,-4),(true,2,-1,-2),(true,2,0,0),(false,2,0,0),(false,1,0,0),(false,0,0,0)]
def tc : Array Q := #[(false,0,0,0),(true,0,0,0),(true,0,-1,0),(false,0,-1,0),(false,1,-1,0),(false,2,-1,0),(true,2,-1,0),(true,2,-2,-2),(false,2,-2,-2),(false,1,-2,-2),(true,1,-2,-2),(true,1,-1,-1),(false,1,-1,-1),(false,0,-1,-1),(true,0,-1,-1),(true,0,0,-1),(false,0,0,-1),(false,1,0,-1),(false,2,0,-1),(true,2,0,-1),(true,2,-1,-3),(false,2,-1,-3),(false,1,-1,-3),(true,1,-1,-3),(true,1,-2,-4),(false,1,-2,-4),(false,2,-2,-4),(true,2,-2,-4),(true,2,-1,-2),(true,2,0,0),(false,2,0,0),(false,1,0,0),(false,0,0,0),(true,0,0,0),(true,0,-1,0),(false,0,-1,0),(false,1,-1,0),(true,1,-1,0),(true,1,-2,-1),(false,1,-2,-1),(false,2,-2,-1),(true,2,-2,-1),(true,2,-1,1),(false,2,-1,1),(false,1,-1,1),(false,0,-1,1),(true,0,-1,1),(true,0,0,1),(false,0,0,1),(false,1,0,1),(false,2,0,1),(true,2,0,1),(true,2,-1,-1),(true,2,-2,-3),(false,2,-2,-3),(false,1,-2,-3),(true,1,-2,-3),(true,1,-1,-2),(false,1,-1,-2),(false,2,-1,-2),(true,2,-1,-2),(true,2,0,0),(false,2,0,0),(false,1,0,0),(false,0,0,0)]

set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def same (i j : Nat) : Prop := (i=0 ∧ j=32) ∨ (i=1 ∧ j=33) ∨ (i=2 ∧ j=34) ∨ (i=3 ∧ j=35) ∨ (i=4 ∧ j=36) ∨ (i=28 ∧ j=60) ∨ (i=29 ∧ j=61) ∨ (i=30 ∧ j=62) ∨ (i=31 ∧ j=63)
instance (i j : Nat) : Decidable (same i j) := by unfold same; infer_instance
theorem astep : ∀ i : Fin 32, push ta[i.val]! wa[i.val]! = ta[i.val+1]! := by decide +kernel
theorem cstep : ∀ i : Fin 64, push tc[i.val]! wc[i.val]! = tc[i.val+1]! := by decide +kernel
theorem achart : ∀ i j : Fin 32, i.val<j.val → separated ta[i.val]! ta[j.val]! := by decide +kernel
theorem cchart : ∀ i j : Fin 64, i.val<j.val → separated tc[i.val]! tc[j.val]! ∨ same i.val j.val := by decide +kernel

def U (x y : G) : G := y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y
def V (x y : G) : G := x*x*y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹*x⁻¹
def residue (x y : G) : G := U x y * V x y

theorem a_end (x y : G) : pathAt x y wa 32 = (false,residue x y) := by
  norm_num [pathAt,run,start,action,wa,residue,U,V]
  group

theorem b_end (x y : G) : pathAt x y wb 32 = (false,V x y*U x y) := by
  norm_num [pathAt,run,start,action,wb,U,V]
  group

theorem c_end (x y : G) : pathAt x y wc 64 = (false,(U x y*V x y)*(V x y*U x y)⁻¹) := by
  norm_num [pathAt,run,start,action,wc,U,V]
  group

theorem explicit (x y : G) :
    residue x y = (y⁻¹ * x) * ⁅⁅x,y⁻¹⁆,x⁻¹*⁅y,x^2⁆*x⁆ * (y⁻¹*x)⁻¹ := by
  unfold residue U V commutatorElement
  rw [pow_two]
  group

end Ribbon6
