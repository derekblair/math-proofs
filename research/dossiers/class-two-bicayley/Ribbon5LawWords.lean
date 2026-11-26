import HaarClass5Commute

namespace Ribbon5Law
open scoped commutatorElement
variable {G : Type*} [Group G]

def Q (x y : G) := ⁅y,x⁆
def Z (x y : G) := x⁻¹*Q x y*x
def V0 (x y : G) := ⁅y,Q x y⁆
def V1 (x y : G) := x⁻¹*V0 x y*x

def word26 : List (Fin 3) := [1,2,0,0,2,0,2,1,2,1,2,1,2,0,2,0,0,2,1,2,1,2,0,2,1,2]
def word32 : List (Fin 3) := [1,2,0,0,2,0,0,2,1,2,1,1,2,1,2,0,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1]

/-- Path multiplication, starting on a specified rim; 0 and 1 are
the two rim directions and 2 is the spoke. -/
def trace (x y : G) : Bool → List (Fin 3) → G
  | _, [] => 1
  | side, p::w =>
    if p=2 then trace x y (!side) w
    else let g := if side then y else x
         (if p=0 then g else g⁻¹) * trace x y side w

theorem rewrite26 (x y : G) : trace x y false word26 = ⁅V1 x y * (Z x y)^2,(Z x y)⁻¹⁆ := by
  norm_num [word26,trace,V1,V0,Z,Q,commutatorElement_def,pow_two]
  group

theorem rewrite32 (x y : G) : trace x y false word32 =
    ⁅(V1 x y*(Z x y)^2)*(V0 x y*(Q x y)^2),(Z x y*Q x y)⁻¹⁆ := by
  norm_num [word32,trace,V1,V0,Z,Q,commutatorElement_def,pow_two]
  group

end Ribbon5Law
#print axioms Ribbon5Law.rewrite26
#print axioms Ribbon5Law.rewrite32
