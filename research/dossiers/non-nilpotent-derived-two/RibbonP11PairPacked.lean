import RibbonP11Pair
namespace RibbonP11Pair
open RibbonStationaryWord RibbonP11Charts
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def points (z : Parameter) (k : Count) : List (Flat F) :=
  (spec k).T.scanl
    (flatStep z.1 (z.1^9) z.2 (z.2^9)
      (if z.1=1 then 1 else 0) (if z.1=1 then 0 else 1))
    (false,1,0)

theorem points_length (z : Parameter) (k : Count) : (points z k).length=65 := by
  simpa [points,List.length_scanl] using congrArg Nat.succ (all_valid k).1

theorem points_at (z : Parameter) (k : Count) (i : Fin 64) :
    (points z k)[i.val]'(by rw [points_length]; omega) = point z k i := by
  unfold points point flatPosition
  exact List.getElem_scanl _

def key (s : Flat F) : Nat := (if s.1 then 121 else 0) + 11*s.2.1.val + s.2.2.val

theorem keys_equal {s t : Flat F} (h : s=t) : key s=key t := congrArg key h

def row (z : Parameter) (k : Count) : Array Nat := ((points z k).map key).toArray

theorem row_at (z : Parameter) (k : Count) (i : Fin 64) : (row z k)[i.val]! = key (point z k i) := by
  have l : i.val < (points z k).length := by rw [points_length]; omega
  have h : i.val<(row z k).size := by simpa [row] using l
  rw [getElem!_pos (row z k) i.val h]
  simp only [row, List.getElem_toArray,List.getElem_map,points_at]

def checkRows (z w : Array Nat) (s : Spec) : Bool :=
  (List.range 64).all fun i => (List.range 64).all fun j =>
    !(decide (i<j) && (z[i]! == z[j]!) && (w[i]! == w[j]!)) || decide (IsMate s i j)

theorem rows_sound {a b : Parameter} {k : Count}
    (h : checkRows (row a k) (row b k) (spec k)=true) : property k a b := by
  intro i j lt e f
  have h' := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have h'' := List.all_eq_true.mp h' j.val (List.mem_range.mpr j.isLt)
  simpa only [decide_eq_true lt,row_at,keys_equal e,keys_equal f,
    beq_self_eq_true,Bool.true_and,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h''

end RibbonP11Pair
#print axioms RibbonP11Pair.rows_sound
