import Ribbon6Family
namespace Ribbon7
open Ribbon5Bridge
open scoped commutatorElement
variable {G : Type*} [Group G]
set_option maxRecDepth 32000
set_option maxHeartbeats 0
def wa : Array P := #[1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1]
def ww : Array P := #[1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1]
def wt : Array P := #[1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,1,2]
def ta : Array Q := #[(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,-1,1),(false,-1,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,-2,0),(false,1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(false,0,-1,0),(false,-1,-1,0),(true,-1,-1,0),(true,-1,0,-1),(false,-1,0,-1),(false,0,0,-1),(false,1,0,-1),(true,1,0,-1),(true,1,-1,-2),(false,1,-1,-2),(false,0,-1,-2),(true,0,-1,-2),(true,0,-2,-2),(false,0,-2,-2),(false,1,-2,-2),(true,1,-2,-2),(true,1,-1,-1),(true,1,0,0),(false,1,0,0),(false,0,0,0)]
def tw : Array Q := #[(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,-1,1),(false,-1,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,-2,0),(false,1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(false,0,-1,0),(false,-1,-1,0),(true,-1,-1,0),(true,-1,0,-1),(false,-1,0,-1),(false,0,0,-1),(false,1,0,-1),(true,1,0,-1),(true,1,-1,-2),(false,1,-1,-2),(false,0,-1,-2),(true,0,-1,-2),(true,0,-2,-2),(false,0,-2,-2),(false,1,-2,-2),(true,1,-2,-2),(true,1,-1,-1),(true,1,0,0),(false,1,0,0),(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,-1,1),(false,-1,-1,1),(false,0,-1,1),(true,0,-1,1),(true,0,-2,1),(false,0,-2,1),(false,1,-2,1),(true,1,-2,1),(true,1,-1,2),(false,1,-1,2),(false,0,-1,2),(false,-1,-1,2),(true,-1,-1,2),(true,-1,0,1),(false,-1,0,1),(false,0,0,1),(false,1,0,1),(true,1,0,1),(true,1,-1,0),(true,1,-2,-1),(false,1,-2,-1),(false,0,-2,-1),(true,0,-2,-1),(true,0,-1,-1),(false,0,-1,-1),(false,1,-1,-1),(true,1,-1,-1),(true,1,0,0),(false,1,0,0),(false,0,0,0)]
def tt : Array Q := #[(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,-1,1),(false,-1,-1,1),(false,0,-1,1),(false,1,-1,1),(true,1,-1,1),(true,1,-2,0),(false,1,-2,0),(false,0,-2,0),(true,0,-2,0),(true,0,-1,0),(false,0,-1,0),(false,-1,-1,0),(true,-1,-1,0),(true,-1,0,-1),(false,-1,0,-1),(false,0,0,-1),(false,1,0,-1),(true,1,0,-1),(true,1,-1,-2),(false,1,-1,-2),(false,0,-1,-2),(true,0,-1,-2),(true,0,-2,-2),(false,0,-2,-2),(false,1,-2,-2),(true,1,-2,-2),(true,1,-1,-1),(true,1,0,0),(false,1,0,0),(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,-1,1),(false,-1,-1,1),(false,0,-1,1),(true,0,-1,1),(true,0,-2,1),(false,0,-2,1),(false,1,-2,1),(true,1,-2,1),(true,1,-1,2),(false,1,-1,2),(false,0,-1,2),(false,-1,-1,2),(true,-1,-1,2),(true,-1,0,1),(false,-1,0,1),(false,0,0,1),(false,1,0,1),(true,1,0,1),(true,1,-1,0),(true,1,-2,-1),(false,1,-2,-1),(false,0,-2,-1),(true,0,-2,-1),(true,0,-1,-1),(false,0,-1,-1),(false,1,-1,-1),(true,1,-1,-1),(true,1,0,0),(false,1,0,0),(false,0,0,0),(false,-1,0,0),(true,-1,0,0),(true,-1,1,-1),(false,-1,1,-1),(false,0,1,-1),(true,0,1,-1),(true,0,2,-1),(false,0,2,-1),(false,-1,2,-1),(false,-2,2,-1),(true,-2,2,-1),(true,-2,1,1),(false,-2,1,1),(false,-1,1,1),(true,-1,1,1),(true,-1,0,2),(false,-1,0,2),(false,0,0,2),(true,0,0,2),(true,0,1,2),(false,0,1,2),(false,-1,1,2),(false,-2,1,2),(true,-2,1,2),(true,-2,2,0),(false,-2,2,0),(false,-1,2,0),(false,0,2,0),(true,0,2,0),(true,0,1,0),(false,0,1,0),(false,-1,1,0),(true,-1,1,0),(true,-1,0,1),(false,-1,0,1),(false,0,0,1),(true,0,0,1),(true,0,1,1),(true,0,2,1),(false,0,2,1),(false,-1,2,1),(false,-2,2,1),(true,-2,2,1),(true,-2,1,3),(false,-2,1,3),(false,-1,1,3),(false,0,1,3),(true,0,1,3),(true,0,0,3),(false,0,0,3),(false,-1,0,3),(true,-1,0,3),(true,-1,1,2),(false,-1,1,2),(false,-2,1,2),(true,-2,1,2),(true,-2,2,0),(false,-2,2,0),(false,-1,2,0),(false,0,2,0),(true,0,2,0),(true,0,1,0),(true,0,0,0),(false,0,0,0)]
theorem astep : ∀ i : Fin 32, push ta[i.val]! wa[i.val]! = ta[i.val+1]! := by decide +kernel
theorem wstep : ∀ i : Fin 64, push tw[i.val]! ww[i.val]! = tw[i.val+1]! := by decide +kernel
theorem tstep : ∀ i : Fin 128, push tt[i.val]! wt[i.val]! = tt[i.val+1]! := by decide +kernel
def mw (i j : Nat) : Prop := (i=0 ∧ j=32) ∨ (i=1 ∧ j=33) ∨ (i=2 ∧ j=34) ∨ (i=3 ∧ j=35) ∨ (i=4 ∧ j=36) ∨ (i=5 ∧ j=37) ∨ (i=29 ∧ j=61) ∨ (i=30 ∧ j=62) ∨ (i=31 ∧ j=63)
instance (i j : Nat) : Decidable (mw i j) := by unfold mw; infer_instance
def mt (i j : Nat) : Prop := (i=0 ∧ j=32) ∨ (i=0 ∧ j=64) ∨ (i=32 ∧ j=64) ∨ (i=1 ∧ j=33) ∨ (i=1 ∧ j=65) ∨ (i=33 ∧ j=65) ∨ (i=2 ∧ j=34) ∨ (i=2 ∧ j=66) ∨ (i=34 ∧ j=66) ∨ (i=3 ∧ j=35) ∨ (i=4 ∧ j=36) ∨ (i=5 ∧ j=37) ∨ (i=29 ∧ j=61) ∨ (i=30 ∧ j=62) ∨ (i=31 ∧ j=63) ∨ (i=48 ∧ j=98) ∨ (i=49 ∧ j=99) ∨ (i=50 ∧ j=100) ∨ (i=86 ∧ j=118) ∨ (i=87 ∧ j=119) ∨ (i=88 ∧ j=120) ∨ (i=89 ∧ j=121) ∨ (i=90 ∧ j=122) ∨ (i=91 ∧ j=123) ∨ (i=92 ∧ j=124) ∨ (i=93 ∧ j=125) ∨ (i=94 ∧ j=126)
instance (i j : Nat) : Decidable (mt i j) := by unfold mt; infer_instance
theorem achart : ∀ i j : Fin 32, i.val < j.val → separated ta[i.val]! ta[j.val]! := by decide +kernel
theorem wchart : ∀ i j : Fin 64, i.val < j.val → separated tw[i.val]! tw[j.val]! ∨ mw i.val j.val := by decide +kernel
theorem tchart : ∀ i j : Fin 128, i.val < j.val → separated tt[i.val]! tt[j.val]! ∨ mt i.val j.val := by decide +kernel
def U (x y : G) : G := x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x
def V (x y : G) : G := x*y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹
def K (x y : G) : G := x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x*x*y⁻¹*x⁻¹*y⁻¹*x
def R (x y : G) : G := U x y * V x y
def Z (x y : G) : G := ⁅U x y,V x y⁆
theorem a_end (x y : G) : pathAt x y wa 32=(false,R x y) := by
  norm_num [pathAt,run,start,action,wa,R,Z,K,U,V,commutatorElement_def] <;> group
theorem w_end (x y : G) : pathAt x y ww 64=(false,Z x y) := by
  norm_num [pathAt,run,start,action,ww,R,Z,K,U,V,commutatorElement_def] <;> group
theorem t_end (x y : G) : pathAt x y wt 128=(false,Z x y * (K x y)⁻¹ * (Z x y)⁻¹ * K x y) := by
  norm_num [pathAt,run,start,action,wt,R,Z,K,U,V,commutatorElement_def] <;> group

end Ribbon7
