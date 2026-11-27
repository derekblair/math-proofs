import Ribbon5Bridge64

namespace RibbonDumbbell
abbrev Tag := Fin 95
abbrev Dot := Fin 32
abbrev Dir := Fin 6
abbrev Z := Int × Int
abbrev Mode := Fin 5

def aTag (i : Dot) : Tag := ⟨i.val, by have := i.isLt; omega⟩
def bTag (i : Dot) : Tag := ⟨32+i.val, by have := i.isLt; omega⟩

def pTag (i : Fin 33) : Tag :=
  if i.val = 0 then aTag 0 else if h : i.val = 32 then bTag 0 else
    ⟨63+i.val, by have := i.isLt; omega⟩

def dot (i : Nat) : Dot := ⟨i%32,by omega⟩
def pdot (i : Nat) : Fin 33 := ⟨i%33,by omega⟩

/-- Directions: A+, A−, B+, B−, P+, P−. -/
def src (d : Dir) (i : Dot) : Tag :=
  ![aTag i, aTag (dot (32-i.val)), bTag i, bTag (dot (32-i.val)),
      pTag (pdot i.val),pTag (pdot (32-i.val))] d
def dst (d : Dir) (i : Dot) : Tag :=
  ![aTag (dot (i.val+1)), aTag (dot (31-i.val)),
      bTag (dot (i.val+1)), bTag (dot (31-i.val)),
      pTag (pdot (i.val+1)),pTag (pdot (31-i.val))] d

def gain (a b : Z) (d : Dir) (i : Dot) : Z :=
  ![if i.val == 31 then a else 0, if i.val == 0 then -a else 0,
    if i.val == 31 then b else 0, if i.val == 0 then -b else 0, 0,0] d

def alter (d : Dir) : Dir := ![1,0,3,2,5,4] d
def reverseDot (i : Dot) : Dot := dot (31-i.val)
def revDir (d : Dir) : Prop := d=1 ∨ d=3 ∨ d=5
instance (d : Dir) : Decidable (revDir d) := by unfold revDir; infer_instance

def dirs (m : Mode) : Array Dir :=
  ![#[0,4,2,5,1,4,3,5], #[0,4,2,5], #[0,4,3,5], #[0], #[2]] m
def len (m : Mode) : Nat := (dirs m).size*32
def stepDir (m : Mode) (i : Nat) : Dir := (dirs m)[i/32]!
def next (m : Mode) (i : Fin (len m)) : Fin (len m) :=
  ⟨(i.val+1)%len m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def shiftA (m : Mode) : Z := ![(1,0),(1,0),(1,0),0,0] m
def shiftB (m : Mode) : Z := ![(0,1),(-1,0),(1,0),0,0] m

def levels (m : Mode) (i : Nat) : Z :=
  let q := i/32
  let r := i%32
  if m.val == 0 then
    (#[0,(1,0),(1,0),(1,1),if r==0 then (1,1) else (0,1),
        (0,1),if r==0 then (0,1) else 0,0] : Array Z)[q]!
  else if m.val == 1 then (#[0,(1,0),(1,0),0] : Array Z)[q]!
  else if m.val == 2 then (#[0,(1,0),if r==0 then (1,0) else 0,0] : Array Z)[q]!
  else 0

def site (m : Mode) (i : Nat) : Tag := src (stepDir m i) (dot i)
def indexCode (m : Mode) (i : Nat) : Nat :=
  4*(site m i).val + (levels m i).1.toNat + 2*(levels m i).2.toNat

end RibbonDumbbell
