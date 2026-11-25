import Lean

/-!
Counterexample to Question 4 in Shahid Hussain, *Decision trees for
subword-closed languages over arbitrary finite alphabets*, arXiv:2611.27454v1,
Sections 2 and 6 (https://arxiv.org/html/2611.27454v1#S6).
-/

namespace HussainMembership

def zeroCount : List Bool → Nat
  | [] => 0
  | x :: xs => (if x then 0 else 1) + zeroCount xs

def language (w : List Bool) : Prop := zeroCount w ≤ 1

theorem zeroCount_sublist {u v : List Bool} (h : List.Sublist u v) :
    zeroCount u ≤ zeroCount v := by
  induction h with
  | slnil => decide
  | cons a h ih => cases a <;> simp [zeroCount] <;> omega
  | cons_cons a h ih => cases a <;> simp [zeroCount] <;> omega

theorem subwordClosed {u v : List Bool} (h : List.Sublist u v) (hv : language v) :
    language u := Nat.le_trans (zeroCount_sublist h) hv

inductive Pos where
  | first | second | third
  deriving DecidableEq

structure Three where
  a : Bool
  b : Bool
  c : Bool

def letter (w : Three) : Pos → Bool
  | .first => w.a
  | .second => w.b
  | .third => w.c

def accepts (w : Three) : Bool := (w.a && w.b) || (w.a && w.c) || (w.b && w.c)

theorem matchesLanguage (w : Three) :
    accepts w = true ↔ language [w.a,w.b,w.c] := by
  unfold language
  rcases w with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- The unlabeled root is suppressed. An absent branch has no complete path. -/
inductive DTree where
  | missing
  | leaf (answer : Bool)
  | query (coord : Pos) (onZero onOne : DTree)

def DTree.depth : DTree → Nat
  | .missing | .leaf _ => 0
  | .query _ l r => max l.depth r.depth + 1

def DTree.eval : DTree → Three → Option Bool
  | .missing, _ => none
  | .leaf x, _ => some x
  | .query i l r, w => if letter w i then r.eval w else l.eval w

def DCorrect (t : DTree) : Prop := ∀ w, t.eval w = some (accepts w)

theorem ambiguousAfter (i j : Pos) :
    ∃ x y : Three, letter x i = true ∧ letter y i = true ∧
      letter x j = letter y j ∧ accepts x ≠ accepts y := by
  cases i <;> cases j
  · exact ⟨⟨true, false, false⟩, ⟨true, false, true⟩, by decide⟩
  · exact ⟨⟨true, false, false⟩, ⟨true, false, true⟩, by decide⟩
  · exact ⟨⟨true, false, false⟩, ⟨true, true, false⟩, by decide⟩
  · exact ⟨⟨false, true, false⟩, ⟨false, true, true⟩, by decide⟩
  · exact ⟨⟨false, true, false⟩, ⟨false, true, true⟩, by decide⟩
  · exact ⟨⟨false, true, false⟩, ⟨true, true, false⟩, by decide⟩
  · exact ⟨⟨false, false, true⟩, ⟨false, true, true⟩, by decide⟩
  · exact ⟨⟨false, false, true⟩, ⟨true, false, true⟩, by decide⟩
  · exact ⟨⟨false, false, true⟩, ⟨false, true, true⟩, by decide⟩

abbrev Path := List (Pos × Bool) × Bool

def compatible (p : Path) (w : Three) : Bool :=
  p.1.all (fun entry => letter w entry.1 == entry.2)

def equalPair (i j : Pos) (b : Bool) : Path := ([(i,b),(j,b)],b)

def paths : List Path :=
  [equalPair .first .second false, equalPair .first .second true,
   equalPair .first .third false, equalPair .first .third true,
   equalPair .second .third false, equalPair .second .third true]

theorem pathCoverage (w : Three) : ∃ p, p ∈ paths ∧ compatible p w = true := by
  apply List.any_eq_true.mp
  rcases w with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem pathCorrect (w : Three) (p : Path) (hp : p ∈ paths)
    (hm : compatible p w = true) : p.2 = accepts w := by
  have h : paths.all (fun q => !compatible q w || q.2 == accepts w) = true := by
    rcases w with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;> decide
  have h' := List.all_eq_true.mp h p hp
  simpa [hm] using h'

theorem pathDepth (p : Path) (h : p ∈ paths) : p.1.length ≤ 2 := by
  have ha : paths.all (fun q => decide (q.1.length ≤ 2)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp ha p h)

/-- Complete paths in the subtree entered by the unique unlabeled root edge. -/
inductive DPath : DTree → List (Pos × Bool) → Bool → Prop
  | leaf (b) : DPath (.leaf b) [] b
  | zero {i l r qs b} : DPath l qs b → DPath (.query i l r) ((i,false)::qs) b
  | one {i l r qs b} : DPath r qs b → DPath (.query i l r) ((i,true)::qs) b

theorem path_evaluates {t qs b} {w : Three} (p : DPath t qs b)
    (h : compatible (qs,b) w = true) : t.eval w = some b := by
  induction p with
  | leaf => rfl
  | @zero i l r qs b hp ih =>
    have h' : letter w i = false ∧ compatible (qs,b) w = true := by
      simpa [compatible] using h
    simpa [DTree.eval,h'.1] using ih h'.2
  | @one i l r qs b hp ih =>
    have h' : letter w i = true ∧ compatible (qs,b) w = true := by
      simpa [compatible] using h
    simpa [DTree.eval,h'.1] using ih h'.2

theorem eval_path {t : DTree} {w : Three} {b : Bool} (h : t.eval w = some b) :
    ∃ qs, DPath t qs b ∧ compatible (qs,b) w = true := by
  induction t with
  | missing => simp [DTree.eval] at h
  | leaf d =>
    have hd : d = b := Option.some.inj h
    subst d
    exact ⟨[], .leaf b, rfl⟩
  | query i l r ihl ihr =>
    cases hi : letter w i
    · obtain ⟨qs,hp,hm⟩ := ihl (by simpa [DTree.eval,hi] using h)
      exact ⟨(i,false)::qs, .zero hp, by simpa [compatible,hi] using hm⟩
    · obtain ⟨qs,hp,hm⟩ := ihr (by simpa [DTree.eval,hi] using h)
      exact ⟨(i,true)::qs, .one hp, by simpa [compatible,hi] using hm⟩

theorem complete_le_depth {t : DTree} {qs : List (Pos × Bool)} {b : Bool}
    (p : DPath t qs b) : qs.length ≤ t.depth := by
  induction p with
  | leaf => simp [DTree.depth]
  | @zero i l r qs b hp ih =>
    have hh := Nat.le_max_left l.depth r.depth
    simp only [List.length_cons,DTree.depth]
    omega
  | @one i l r qs b hp ih =>
    have hh := Nat.le_max_right l.depth r.depth
    simp only [List.length_cons,DTree.depth]
    omega

/-- Membership coverage, correctness, and depth are all measured on
    complete paths, as in Hussain's Definitions 3–8.  The branch 'missing'
    supplies no complete path. Any source deterministic tree embeds in this
    grammar after removing its unique, unlabeled root edge. -/
def DetAtMost (k : Nat) : Prop :=
  ∃ t : DTree,
    (∀ w, ∃ qs b, DPath t qs b ∧ compatible (qs,b) w = true) ∧
    (∀ w qs b, DPath t qs b → compatible (qs,b) w = true → b = accepts w) ∧
    (∀ qs b, DPath t qs b → qs.length ≤ k)

/-- Unfolding a tree gives its list of complete paths. Conversely a list of
    paths is realized by giving each path a separate unlabeled root edge
    and one outgoing edge per letter test on that path. -/
def NDAtMost (k : Nat) : Prop :=
  ∃ ps : List Path,
    (∀ w, ∃ p, p ∈ ps ∧ compatible p w = true) ∧
    (∀ w p, p ∈ ps → compatible p w = true → p.2 = accepts w) ∧
    (∀ p, p ∈ ps → p.1.length ≤ k)

theorem noExactDetTwo : ¬ DetAtMost 2 := by
  rintro ⟨t, htotal, hsound, hbound⟩
  have hc : DCorrect t := by
    intro w
    obtain ⟨qs,b,hp,hm⟩ := htotal w
    have he := path_evaluates hp hm
    rw [hsound w qs b hp hm] at he
    exact he
  have distinguish (x y : Three) (h : accepts x ≠ accepts y)
      (he : t.eval x = t.eval y) : False :=
    h (Option.some.inj ((hc x).symm.trans (he.trans (hc y))))
  cases t with
  | missing =>
    exact distinguish ⟨false,false,false⟩ ⟨true,true,true⟩ (by decide) rfl
  | leaf b =>
    exact distinguish ⟨false,false,false⟩ ⟨true,true,true⟩ (by decide) rfl
  | query i l r =>
    cases r with
    | missing =>
      obtain ⟨x,y,hx,hy,_,hne⟩ := ambiguousAfter i i
      exact distinguish x y hne (by simp [DTree.eval,hx,hy])
    | leaf b =>
      obtain ⟨x,y,hx,hy,_,hne⟩ := ambiguousAfter i i
      exact distinguish x y hne (by simp [DTree.eval,hx,hy])
    | query j lo hi =>
      obtain ⟨x,y,hx,hy,hj,hne⟩ := ambiguousAfter i j
      apply distinguish x y hne
      simp only [DTree.eval,hx,hy,ite_true]
      cases jx : letter x j
      · have jy : letter y j = false := hj.symm.trans jx
        have e : lo.eval x = some (accepts x) := by simpa [DTree.eval,hx,jx] using hc x
        obtain ⟨qs,hp,_⟩ := eval_path e
        have hn := hbound _ _ (DPath.one (DPath.zero hp))
        have hq : qs = [] := by
          simp only [List.length_cons] at hn
          exact List.length_eq_zero_iff.mp (by omega : qs.length = 0)
        subst qs
        have ey : lo.eval y = some (accepts x) := path_evaluates hp rfl
        simpa [jx,jy,ey] using e
      · have jy : letter y j = true := hj.symm.trans jx
        have e : hi.eval x = some (accepts x) := by simpa [DTree.eval,hx,jx] using hc x
        obtain ⟨qs,hp,_⟩ := eval_path e
        have hn := hbound _ _ (DPath.one (DPath.one hp))
        have hq : qs = [] := by
          simp only [List.length_cons] at hn
          exact List.length_eq_zero_iff.mp (by omega : qs.length = 0)
        subst qs
        have ey : hi.eval y = some (accepts x) := path_evaluates hp rfl
        simpa [jx,jy,ey] using e

def fullQuery : DTree :=
  let third := fun a b => DTree.query .third (.leaf (accepts ⟨a,b,false⟩))
                                           (.leaf (accepts ⟨a,b,true⟩))
  let second := fun a => DTree.query .second (third a false) (third a true)
  .query .first (second false) (second true)

theorem fullQueryCorrect : DCorrect fullQuery := by
  intro w
  rcases w with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem exactDetUpper : DetAtMost 3 := by
  refine ⟨fullQuery,?_,?_,?_⟩
  · intro w
    obtain ⟨qs,hp,hm⟩ := eval_path (fullQueryCorrect w)
    exact ⟨qs,accepts w,hp,hm⟩
  · intro w qs b hp hm
    exact Option.some.inj ((path_evaluates hp hm).symm.trans (fullQueryCorrect w))
  · intro qs b hp
    exact Nat.le_trans (complete_le_depth hp) (by decide)

theorem exactNDUpper : NDAtMost 2 := ⟨paths,pathCoverage,pathCorrect,pathDepth⟩

theorem noExactNDOne : ¬ NDAtMost 1 := by
  rintro ⟨ps, htotal, hsound, hbound⟩
  let w : Three := ⟨true,true,true⟩
  obtain ⟨⟨qs,b⟩,hp,hm⟩ := htotal w
  have hb := hsound w (qs,b) hp hm
  have hn := hbound (qs,b) hp
  change qs.length ≤ 1 at hn
  have hbTrue : b = true := hb
  have wrong : ∃ v : Three, compatible (qs,b) v = true ∧ accepts v = false := by
    cases qs with
    | nil => exact ⟨⟨false,false,false⟩,⟨rfl,rfl⟩⟩
    | cons q rs =>
      obtain ⟨i,z⟩ := q
      cases rs with
      | nil =>
        have hz : z=true := by cases i <;> simpa [compatible,w,letter] using hm.symm
        subst z
        cases i
        · exact ⟨⟨true,false,false⟩,⟨rfl,rfl⟩⟩
        · exact ⟨⟨false,true,false⟩,⟨rfl,rfl⟩⟩
        · exact ⟨⟨false,false,true⟩,⟨rfl,rfl⟩⟩
      | cons q rs => simp at hn
  obtain ⟨v,hv,hf⟩ := wrong
  have h := hsound v (qs,b) hp hv
  rw [hf,hbTrue] at h
  contradiction

theorem nontrivialAndInfinite :
    (∀ n, language (List.replicate n true)) ∧ ¬ language [false,false] := by
  constructor
  · intro n
    have ht : zeroCount (List.replicate n true) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ,zeroCount,ih]
    simp [language,ht]
  · unfold language
    decide

theorem question4Counterexample :
    (∀ ⦃u v : List Bool⦄, List.Sublist u v → language v → language u) ∧
    (∀ w : Three, accepts w = true ↔ language [w.a,w.b,w.c]) ∧
    NDAtMost 2 ∧ ¬ NDAtMost 1 ∧ DetAtMost 3 ∧ ¬ DetAtMost 2 :=
  ⟨(fun _ _ => subwordClosed),matchesLanguage,exactNDUpper,noExactNDOne,exactDetUpper,noExactDetTwo⟩
#print axioms question4Counterexample

end HussainMembership
