import PetersenArithmetic
open scoped BigOperators
namespace PetersenStability

abbrev V := Fin 15
abbrev C := Fin 20

def pair (v : V) : Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(0,0),(0,0),(0,0),(0,0),(0,0)] v

def contains (v : V) (i : Fin 5) : Bool :=
  ((pair v).1 == i) || ((pair v).2 == i)

def indices (c : C) : Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,0),(1,2),(1,3),(1,4),(2,0),(2,1),(2,3),(2,4),
    (3,0),(3,1),(3,2),(3,4),(4,0),(4,1),(4,2),(4,3)] c

def extra (i : Fin 5) : V := ⟨10+i.val, by omega⟩

def full (c : C) (v : V) : Bool :=
  v.val < 10 && !contains v (indices c).1 && !contains v (indices c).2

def split (c : C) (v : V) : Bool :=
  v.val < 10 && !contains v (indices c).1 && contains v (indices c).2

def F (c : C) : Finset V := Finset.univ.filter (full c · = true)
def P (c : C) : Finset V := Finset.univ.filter (split c · = true)

def edge (a b : V) : Bool :=
  a.val < b.val && a.val < 10 &&
  if b.val < 10 then !contains a (pair b).1 && !contains a (pair b).2
  else contains a ⟨b.val-10, by omega⟩

def E : Finset (V × V) := Finset.univ.filter (fun e => edge e.1 e.2 = true)

def outside (v : V) : Bool := 10 ≤ v.val

def anchor (c : C) : V := extra (indices c).1
def side (c : C) : V := extra (indices c).2

def cover (c : C) (a b : V) : Bool :=
  (full c a && split c b) || (split c a && (full c b || b == side c))

def support (c : C) (v : V) : Bool :=
  full c v || split c v || v == anchor c || v == side c

theorem countF : ∀ c : C, (F c).card = 3 := by decide
theorem countP : ∀ c : C, (P c).card = 3 := by decide
theorem countF_at : ∀ v : V, v.val < 10 →
    (Finset.univ.filter (fun c : C => full c v = true)).card = 6 := by decide
theorem countAnchor : ∀ v : V, 10 ≤ v.val →
    (Finset.univ.filter (fun c : C => anchor c = v)).card = 4 := by decide
theorem countSide : ∀ v : V, 10 ≤ v.val →
    (Finset.univ.filter (fun c : C => side c = v)).card = 4 := by decide
theorem countCover : ∀ a b : V, edge a b = true →
    (Finset.univ.filter (fun c : C => cover c a b = true)).card =
      (if b.val < 10 then 4 else 3) := by decide
theorem exactCover : ∀ c : C, ∀ a b : V, edge a b = true →
    ((support c a && support c b) = cover c a b) := by decide

theorem flipCross : ∀ c : C, ∀ a b : V,
    full c a = true → split c b = true → edge a b = true ∨ edge b a = true →
    (edge a b = true ↔ a.val < b.val) := by decide

end PetersenStability
