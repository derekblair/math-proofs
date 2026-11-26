import HaarBound16
import Mathlib.Data.ZMod.Basic

namespace HaarSharpCore

@[ext] structure H where
  a : ZMod 5
  b : ZMod 5
  c : ZMod 5
  deriving DecidableEq
def mul (p q : H) : H :=
  ⟨p.a+q.a,p.b+q.b,p.c+q.c+p.a*q.b⟩
def inv (p : H) : H := ⟨-p.a,-p.b,-p.c+p.a*p.b⟩
def ident : H := ⟨0,0,0⟩
instance : Group H where
  mul := mul
  inv := inv
  one := ident
  mul_assoc a b c := by
    change mul (mul a b) c = mul a (mul b c)
    ext <;> simp only [mul] <;> ring
  one_mul a := by change mul ident a=a; ext <;> simp [mul,ident]
  mul_one a := by change mul a ident=a; ext <;> simp [mul,ident]
  inv_mul_cancel a := by
    change mul (inv a) a = ident
    ext <;> simp only [mul,inv,ident] <;> ring

def x : H := ⟨1,0,0⟩
def y : H := ⟨0,1,0⟩
def z : H := ⟨0,0,1⟩

theorem rel : x*y=y*x*z := by decide
theorem cx : Commute z x := by change z*x=x*z; decide
theorem cy : Commute z y := by change z*y=y*z; decide
theorem nz : (z : H) ≠ (1 : H) := by decide

def port (i : Fin 3) : H := if i=0 then 1 else if i=1 then x else y

def signPort (i : ℕ) (p : Fin 3) : H := if i%2=0 then port p else (port p)⁻¹

def prodFrom : ℕ → List (Fin 3) → H
  | _,[] => 1
  | i,p::ps => signPort i p * prodFrom (i+1) ps

def good : List (Fin 3) → Bool
  | [] => true
  | [_] => true
  | p::q::ps => p != q && good (q::ps)

def words : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => ([0,1,2] : List (Fin 3)).flatMap (fun p => (words n).map (p::·))

theorem words_all (a : List (Fin 3)) : a ∈ words a.length := by
  induction a with
  | nil => simp [words]
  | cons p l ih =>
    apply List.mem_flatMap.mpr
    refine ⟨p,?_,List.mem_map.mpr ⟨l,ih,rfl⟩⟩
    revert p
    decide

def notClosed (p : List (Fin 3)) : Bool := !good p || ((prodFrom 0 p != (1 : H)) && (prodFrom 1 p != (1 : H)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem check4 : (words 4).all notClosed = true := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem check8 : (words 8).all notClosed = true := by decide

set_option maxRecDepth 15000 in
set_option maxHeartbeats 2000000 in
theorem check6 : (words 6).all notClosed = true := by decide

theorem no_word (L : List (Fin 3)) (h : L.length=4 ∨ L.length=6 ∨ L.length=8)
    (g : good L = true) : prodFrom 0 L ≠ (1 : H) ∧ prodFrom 1 L ≠ (1 : H) := by
  have hm := words_all L
  have c : (words L.length).all notClosed=true := by
    rcases h with w|w|w
    · rw [w]; exact check4
    · rw [w]; exact check6
    · rw [w]; exact check8
  have t := List.all_eq_true.mp c L hm
  simpa [notClosed,g] using t

end HaarSharpCore

#print axioms HaarSharpCore.no_word
