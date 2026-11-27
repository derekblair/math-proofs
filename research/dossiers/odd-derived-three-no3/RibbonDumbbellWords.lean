import RibbonDumbbellLift

namespace RibbonDumbbell
open Ribbon5Bridge
variable {G : Type*} [Group G]

def atWord (x y : G) (u : Bool × G) (w : Array P) (i : Nat) : Bool × G :=
  run x y u (w.toList.take i)

@[simp] theorem atWord0 (x y : G) (u : Bool × G) (w : Array P) :
    atWord x y u w 0 = u := rfl

theorem adj_at (x y : G) (u : Bool × G) (w : Array P) (i : Nat) (h : i < w.size) :
    Ribbon.Adj x y (atWord x y u w i) (atWord x y u w (i+1)) := by
  have hh : i < w.toList.length := by simpa using h
  have T : atWord x y u w (i+1) = action x y (atWord x y u w i) w[i] := by
    unfold atWord
    rw [List.take_succ_eq_append_getElem hh,run_append]
    simp [run]
  rw [T]
  exact action_adj x y _ _

structure Words where
  a : Array P
  b : Array P
  p : Array P
  aSize : a.size=32
  bSize : b.size=32
  pSize : p.size=32

def terminus (x y : G) (u : Bool × G) (W : Words) : Bool × G :=
  atWord x y u W.p 32

def wordPoint (x y : G) (u : Bool × G) (W : Words) (i : Tag) : Bool × G :=
  if i.val < 32 then atWord x y u W.a i.val
  else if i.val < 64 then atWord x y (terminus x y u W) W.b (i.val-32)
  else atWord x y u W.p (i.val-63)

def displacement (x y : G) (u : Bool × G) (w : Array P) : G :=
  (atWord x y u w 32).2 * u.2⁻¹

theorem displaced (x y : G) (u : Bool × G) (w : Array P)
    (side : (atWord x y u w 32).1 = u.1) :
    atWord x y u w 32 = shift (displacement x y u w) u := by
  apply Prod.ext
  · exact side
  · simp [shift,displacement,mul_assoc]

theorem point_A (x y : G) (u : Bool × G) (W : Words) (i : Dot) :
    wordPoint x y u W (aTag i) = atWord x y u W.a i.val := by
  simp [wordPoint,aTag,i.isLt]

theorem point_B (x y : G) (u : Bool × G) (W : Words) (i : Dot) :
    wordPoint x y u W (bTag i) = atWord x y (terminus x y u W) W.b i.val := by
  have h : ¬32+i.val < 32 := by omega
  have h' : 32+i.val < 64 := by have := i.isLt; omega
  simp [wordPoint,bTag,h,h']

theorem point_P (x y : G) (u : Bool × G) (W : Words) (i : Fin 33) :
    wordPoint x y u W (pTag i) = atWord x y u W.p i.val := by
  unfold pTag
  split_ifs with h h'
  · rw [point_A,h]
    rfl
  · rw [point_B,h']
    rfl
  · have M : ¬63+i.val<32 := by omega
    have N : ¬63+i.val<64 := by omega
    simp [wordPoint,M,N]

private theorem loop_step (x y : G) (u : Bool × G) (w : Array P)
    (len : w.size=32) (side : (atWord x y u w 32).1 = u.1) (i : Dot) :
    Ribbon.Adj x y (atWord x y u w i.val)
      (shift (if i.val == 31 then displacement x y u w else 1)
        (atWord x y u w (dot (i.val+1)).val)) := by
  have H := adj_at x y u w i.val (by simpa [len] using i.isLt)
  by_cases q : i.val=31
  · have t : (dot (i.val+1)).val = 0 := by simp [dot,q]
    rw [t,atWord0]
    simp only [q,beq_self_eq_true,ite_true]
    rw [←displaced x y u w side]
    simpa [q] using H
  · have t : (dot (i.val+1)).val = i.val+1 := by
      unfold dot
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [t]
    simpa [q,shift] using H

/-- Construct the complete forward arc witness directly from three actual port
words. The bridge may switch rims; each loop must preserve its own initial rim. -/
theorem forward_words (x y : G) (u : Bool × G) (W : Words)
    (sideA : (atWord x y u W.a 32).1 = u.1)
    (sideB : (atWord x y (terminus x y u W) W.b 32).1 = (terminus x y u W).1) :
    Forward x y (displacement x y u W.a) (displacement x y (terminus x y u W) W.b)
      (wordPoint x y u W) := by
  constructor
  · intro i
    change Ribbon.Adj x y (wordPoint x y u W (aTag i))
      (shift (if i.val == 31 then displacement x y u W.a else 1)
        (wordPoint x y u W (aTag (dot (i.val+1)))))
    rw [point_A,point_A]
    exact loop_step x y u W.a W.aSize sideA i
  · intro i
    change Ribbon.Adj x y (wordPoint x y u W (bTag i))
      (shift (if i.val == 31 then displacement x y (terminus x y u W) W.b else 1)
        (wordPoint x y u W (bTag (dot (i.val+1)))))
    rw [point_B,point_B]
    exact loop_step x y _ W.b W.bSize sideB i
  · intro i
    change Ribbon.Adj x y (wordPoint x y u W (pTag (pdot i.val)))
      (wordPoint x y u W (pTag (pdot (i.val+1))))
    rw [point_P,point_P]
    have t : (pdot i.val).val=i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
    have s : (pdot (i.val+1)).val=i.val+1 := Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [t,s]
    exact adj_at x y u W.p i.val (by simpa [W.pSize] using i.isLt)

#print axioms forward_words
end RibbonDumbbell
