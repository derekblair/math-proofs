import HaarSharpPortGeometry
import Mathlib.Data.ZMod.Basic

namespace HaarDerivedGirth22
open HaarSharpPortGeometry
open HaarSharpLamp (Row words scan compatible compat_members scan_good)
abbrev S := ZMod 13
abbrev L := Bool → S → ZMod 5

structure G where
  left : L
  right : S

@[ext] theorem G.ext' {a b : G} (hl : ∀ t j, a.left t j = b.left t j)
    (hr : a.right = b.right) : a = b := by
  cases a; cases b; congr; funext t j; exact hl t j

def mul (a b : G) : G :=
  ⟨fun t j => a.left t j + b.left t (j-a.right), a.right+b.right⟩

def unit : G := ⟨fun _ _ => 0,0⟩

def inv (a : G) : G := ⟨fun t j => -(a.left t (j+a.right)), -a.right⟩

instance : Group G where
  mul := mul
  one := unit
  inv := inv
  mul_assoc := by
    intro a b c
    apply G.ext'
    · intro t j; change (mul (mul a b) c).left t j = (mul a (mul b c)).left t j
      simp [mul,sub_sub,add_assoc]
    · change (mul (mul a b) c).right = (mul a (mul b c)).right
      simp [mul,add_assoc]
  one_mul := by
    intro a; apply G.ext'
    · intro t j; change (mul unit a).left t j = a.left t j; simp [mul,unit]
    · change (mul unit a).right = a.right; simp [mul,unit]
  mul_one := by
    intro a; apply G.ext'
    · intro t j; change (mul a unit).left t j = a.left t j; simp [mul,unit]
    · change (mul a unit).right = a.right; simp [mul,unit]
  inv_mul_cancel := by
    intro a; apply G.ext'
    · intro t j; change (mul (inv a) a).left t j = unit.left t j
      simp [mul,inv,unit,sub_neg_eq_add]
    · change (mul (inv a) a).right = unit.right
      simp [mul,inv,unit]

def lamp (b : Bool) : L := fun c j => if b = c ∧ j = 0 then 1 else 0

def port : Fin 3 → G := fun c =>
  if c = 0 then 1 else if c = 1 then ⟨lamp false,1⟩ else ⟨lamp true,4⟩

def x : G := port 1
def y : G := port 2

def key (a : G) : Nat :=
  (List.ofFn (fun j : Fin 13 => (a.left false (j.val : S)).val) ++
    List.ofFn (fun j : Fin 13 => (a.left true (j.val : S)).val)).foldl
      (fun acc q => 5*acc+q) a.right.val


theorem port0 : port 0 = 1 := by rfl

def row (w : List (Fin 3)) : Row :=
  ⟨key (value port true w), w.head?, w.getLast?⟩
def table (n : Nat) : List Row :=
  List.insertionSort HaarSharpLamp.rankLe ((words n none).map row)

theorem cert_sound {n : Nat} (good : scan (table n) = true) {u v : List (Fin 3)}
    (hu : u ∈ words n none) (hv : v ∈ words n none)
    (he : value port true u = value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  have sorted : (table n).Pairwise (fun a b => a.k ≤ b.k) := by
    unfold table
    exact List.pairwise_insertionSort HaarSharpLamp.rankLe _
  have mem (w : List (Fin 3)) (hw : w ∈ words n none) : row w ∈ table n :=
    (List.perm_insertionSort _ _).mem_iff.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have c := compat_members (scan_good _ good sorted) (mem _ hu) (mem _ hv)
  simpa [compatible,row,he] using c

end HaarDerivedGirth22
#print axioms HaarDerivedGirth22.cert_sound
