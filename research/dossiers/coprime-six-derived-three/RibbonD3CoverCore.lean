import RibbonD3FieldChart
import RibbonD3ExactData

namespace RibbonD3MateData
open RibbonD3Field (label raw Shape)

def sameR (a b : Nat) (r : RRow) : Bool := r.i == a && r.j == b
def sameExact (a b : Nat) (r : ExactRow) : Bool := r.i == a && r.j == b

def hasMate (C : Chart) (E : Array ExactRow) (a b : Nat) : Bool :=
  (64 ≤ b && C.rows.any (sameR a b)) || E.any (sameExact a b)

/-- Checked against the compact map in a frozen affine field chart. -/
def checkCover (F : RibbonD3Field.Chart) (C : Chart) (E : Array ExactRow) : Bool :=
  (List.range 128).all fun a =>
    (List.range 128).all fun b =>
      !(a < b && F.map[a]! == F.map[b]!) || hasMate C E a b

def repsUnique (F : RibbonD3Field.Chart) : Prop :=
  Function.Injective (fun i : Fin F.reps.size => F.reps[i])

theorem label_eq_map {F : RibbonD3Field.Chart} (S : Shape F) (U : repsUnique F)
    {a b : Fin 128} (h : label (raw F a) = label (raw F b)) :
    F.map[a.val]! = F.map[b.val]! := by
  obtain ⟨ha,ea⟩ := S.2.2 a
  obtain ⟨hb,eb⟩ := S.2.2 b
  let aa : Fin F.reps.size := ⟨F.map[a.val]!,ha⟩
  let bb : Fin F.reps.size := ⟨F.map[b.val]!,hb⟩
  have ea' : F.reps[aa] = label (raw F a) := by
    simpa only [aa,Fin.getElem_fin,getElem!_pos F.reps (F.map[a.val]!) ha] using ea
  have eb' : F.reps[bb] = label (raw F b) := by
    simpa only [bb,Fin.getElem_fin,getElem!_pos F.reps (F.map[b.val]!) hb] using eb
  exact congrArg Fin.val (U (ea'.trans (h.trans eb'.symm)))

theorem cover_sound {F : RibbonD3Field.Chart} (S : Shape F) (U : repsUnique F)
    {C : Chart} {E : Array ExactRow} (H : checkCover F C E = true)
    {a b : Fin 128} (ab : a.val < b.val)
    (hlabel : label (raw F a) = label (raw F b)) :
    (64 ≤ b.val ∧ ∃ i : Fin C.rows.size, C.rows[i].i = a.val ∧ C.rows[i].j = b.val) ∨
      ∃ i : Fin E.size, E[i].i = a.val ∧ E[i].j = b.val := by
  have qa := List.all_eq_true.mp H a.val (by simpa using a.isLt)
  have qab := List.all_eq_true.mp qa b.val (by simpa using b.isLt)
  have ee := label_eq_map S U hlabel
  have hi : hasMate C E a.val b.val = true := by simpa [ab,ee] using qab
  unfold hasMate at hi
  have Hdisj : (64 ≤ b.val ∧ C.rows.any (sameR a.val b.val) = true) ∨ E.any (sameExact a.val b.val) = true := by simpa using hi
  rcases Hdisj with hr|he
  · obtain ⟨i,hi,hp⟩ := Array.any_eq_true.mp hr.2
    left
    exact ⟨hr.1,⟨i,hi⟩, by simpa [sameR] using hp⟩
  · obtain ⟨i,hi,hp⟩ := Array.any_eq_true.mp he
    right
    exact ⟨⟨i,hi⟩, by simpa [sameExact] using hp⟩

#print axioms cover_sound
end RibbonD3MateData
