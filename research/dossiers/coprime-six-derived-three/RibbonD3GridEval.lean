import RibbonD3SignedEval

namespace RibbonD3Grid
open RibbonD3MateData RibbonD3SignedEval
variable {G : Type*} [Group G]

abbrev Coord := Int × Int
abbrev State := Int × Int × List Int

def legal (a : Int) : Prop := a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2

def gstep (keys : Array Coord) (q : State) (a : Int) : Option State := do
  let (x,y,out) := q
  if a.natAbs == 1 then pure (x+a,y,out)
  else
    let s : Int := if a > 0 then 1 else -1
    let z := y+s
    if x == 0 then pure (x,z,out)
    else
      let n ← keys.toList.idxOf? (x,min y z)
      pure (x,z,s*((n : Int)+1)::out)

def indexed (x y : G) (keys : Array Coord) (a : Int) : G :=
  let p := keys[a.natAbs-1]!
  if 0 < a then edge x y p.1 p.2 else (edge x y p.1 p.2)⁻¹

private theorem key_found {keys : Array Coord} {p : Coord} {n : Nat}
    (hn : keys.toList.idxOf? p = some n) : keys[n]! = p := by
  obtain ⟨h,e,_⟩ := List.idxOf?_eq_some_iff.mp hn
  have h' : n < keys.size := by simpa using h
  simpa [getElem!_pos keys n h',Array.getElem_toList] using e

private theorem indexed_pos (x y : G) (keys : Array Coord) (n : Nat) (i j : Int)
    (h : keys[n]! = (i,j)) : indexed x y keys ((n : Int)+1) = edge x y i j := by
  have hn : 0 < (n : Int)+1 := by omega
  have aa : ((n : Int)+1).natAbs-1 = n := by omega
  simp [indexed,hn,aa,h]

private theorem indexed_neg (x y : G) (keys : Array Coord) (n : Nat) (i j : Int)
    (h : keys[n]! = (i,j)) : indexed x y keys (-((n : Int)+1)) = (edge x y i j)⁻¹ := by
  have hn : ¬ 0 < -((n : Int)+1) := by omega
  have aa : (-((n : Int)+1)).natAbs-1 = n := by omega
  unfold indexed
  rw [aa,h,if_neg hn]

private theorem indexed_neg' (x y : G) (keys : Array Coord) (n : Nat) (i j : Int)
    (h : keys[n]! = (i,j)) : indexed x y keys (-1 + -(n : Int)) = (edge x y i j)⁻¹ := by
  rw [show -1 + -(n : Int) = -((n : Int)+1) by omega]
  exact indexed_neg x y keys n i j h

def meaning (x y : G) (keys : Array Coord) (q : State) : G :=
  eval (indexed x y keys) q.2.2.reverse * trans x y q.1 q.2.1

theorem step_sound (x y : G) (keys : Array Coord) {a : Int} (ha : legal a)
    {q w : State} (h : gstep keys q a = some w) :
    meaning x y keys w = meaning x y keys q * letter x y a := by
  obtain ⟨i,j,L⟩ := q
  rcases ha with E|E|E|E
  · subst a
    simp [gstep] at h
    subst w
    simpa [meaning,letter,mul_assoc] using
      congrArg (fun z => eval (indexed x y keys) L.reverse * z) (hor_pos x y i j).symm
  · subst a
    simp [gstep] at h
    subst w
    simpa [meaning,letter,mul_assoc,sub_eq_add_neg] using
      congrArg (fun z => eval (indexed x y keys) L.reverse * z) (hor_neg x y i j).symm
  · subst a
    by_cases zi : i=0
    · subst i
      simp [gstep] at h
      subst w
      simpa [meaning,letter,mul_assoc] using
        congrArg (fun z => eval (indexed x y keys) L.reverse * z) (ver_pos x y 0 j).symm
    · have M : min j (j+1) = j := by omega
      cases E : keys.toList.idxOf? (i,j) with
      | none => simp [gstep,zi,M,E] at h
      | some n =>
        simp [gstep,zi,M,E] at h
        subst w
        simpa [meaning,letter,eval_append,eval,mul_assoc,
          indexed_pos x y keys n i j (key_found E)] using
          congrArg (fun z => eval (indexed x y keys) L.reverse * z) (ver_pos x y i j).symm
  · subst a
    by_cases zi : i=0
    · subst i
      simp [gstep] at h
      subst w
      simpa [meaning,letter,mul_assoc,sub_eq_add_neg] using
        congrArg (fun z => eval (indexed x y keys) L.reverse * z) (ver_neg x y 0 j).symm
    · have M : min j (j + -1) = j + -1 := by omega
      cases E : keys.toList.idxOf? (i,j + -1) with
      | none => simp [gstep,zi,M,E] at h
      | some n =>
        simp [gstep,zi,M,E] at h
        subst w
        simpa [meaning,letter,eval_append,eval,mul_assoc,sub_eq_add_neg,
          indexed_neg' x y keys n i (j + -1) (key_found E)] using
          congrArg (fun z => eval (indexed x y keys) L.reverse * z) (ver_neg x y i j).symm

end RibbonD3Grid
