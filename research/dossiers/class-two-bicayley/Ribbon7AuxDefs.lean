import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fin.VecNotation

namespace Ribbon7Aux
open scoped commutatorElement
variable {G : Type*} [Group G]
def wa : List (Fin 3) := [1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1]
def wb : List (Fin 3) := [0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0]
def wc : List (Fin 3) := [1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1]
def wd : List (Fin 3) := [1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,1,2,1,2,0,2,0,2,0,2,1,1,2,0,2,0,2,0,2,1,1,2,1,2,0,2,1,2,0,2,0,2,1,1,2,0,2,0,0,2,1,2,1,2,1,2,0,2,0,0,2,1,1,2,1,2,0,0,2,1,2,1,2,0,2,1,2,0,2,0,0,2,1,1,2]

def q (x y : G) : G := ⁅x,y⁻¹⁆
def h (x y : G) : G := (x⁻¹ * ⁅y,x^2⁆ * x) * (q x y)⁻¹ * (q x y)⁻¹
def t (x y : G) : G := x*y⁻¹*y⁻¹*x⁻¹*y*x*y*x⁻¹*x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹
def U (x y : G) : G := x⁻¹*y⁻¹*x*x*y⁻¹*x⁻¹*y*x⁻¹*y*x
def V (x y : G) : G := x*y⁻¹*x⁻¹*y⁻¹*x*y*y*x⁻¹
def res (x y : G) : G := U x y*V x y
def delta (x y : G) : G := x*x*y⁻¹*y⁻¹*x⁻¹*y*x*y*x⁻¹*x⁻¹*y*x*y*x⁻¹*x⁻¹*y⁻¹*x*y⁻¹*x*y*x⁻¹*x⁻¹*y*x*x*y⁻¹*x⁻¹*y⁻¹
end Ribbon7Aux
