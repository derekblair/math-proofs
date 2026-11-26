import Ribbon5ChartSound

namespace Ribbon5Bridge

variable {G H : Type*} [Group G] [Group H]

def run (x y : G) (s : Bool × G) (w : List P) : Bool × G :=
  w.foldl (action x y) s

def start (G : Type*) [Group G] : Bool × G := (false,1)

def pathAt (x y : G) (w : Array P) (i : Nat) : Bool × G :=
  run x y (start G) (w.toList.take i)

def shift (g : G) (s : Bool × G) : Bool × G := (s.1,g*s.2)

theorem pathAt_next (x y : G) (w : Array P) {i : Nat} (hi : i<w.size) :
    pathAt x y w (i+1) = action x y (pathAt x y w i) w[i]! := by
  have H : i<w.toList.length := by simpa using hi
  unfold pathAt
  rw [List.take_succ_eq_append_getElem H]
  simp [run,List.foldl_append,getElem!_pos w i hi,Array.getElem_toList]

theorem shift_action (x y g : G) (s : Bool × G) (p : P) :
    action x y (shift g s) p = shift g (action x y s p) := by
  rcases s with ⟨s,v⟩
  cases s <;> fin_cases p <;> simp [action,shift,mul_assoc]

theorem shift_run (x y g : G) (s : Bool × G) (w : List P) :
    run x y (shift g s) w = shift g (run x y s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons p t ih => exact (congrArg (fun k => run x y k t) (shift_action x y g s p)).trans (ih _)

def inversePort (j : P) : P := ![1,0,2] j
def reverseWord (l : List P) : List P := l.reverse.map inversePort

theorem undo_action (x y : G) (s : Bool × G) (j : P) :
    action x y (action x y s j) (inversePort j) = s := by
  rcases s with ⟨s,v⟩
  cases s <;> fin_cases j <;> simp [inversePort,action,mul_assoc]

theorem undo_run (x y : G) (s : Bool × G) (w : List P) :
    run x y (run x y s w) (reverseWord w) = s := by
  induction w generalizing s with
  | nil => rfl
  | cons j t ih =>
    change run x y (run x y (action x y s j) t) (reverseWord (j::t))=s
    simp only [reverseWord,List.reverse_cons,List.map_append,List.map_singleton]
    have E : run x y (run x y (action x y s j) t) (t.reverse.map inversePort ++ [inversePort j]) =
          action x y (run x y (run x y (action x y s j) t) (reverseWord t)) (inversePort j) := by
      simp [run,reverseWord,List.foldl_append]
    rw [E,ih,undo_action]

theorem mapped_run (f : G→*H) (x y : G) (s : Bool × G) (w : List P) :
    (fun u : Bool × G => (u.1,f u.2)) (run x y s w) =
      run (f x) (f y) (s.1,f s.2) w := by
  induction w generalizing s with
  | nil => rfl
  | cons j t ih =>
    change (fun u : Bool × G => (u.1,f u.2)) (run x y (action x y s j) t) =
      run (f x) (f y) (action (f x) (f y) (s.1,f s.2) j) t
    rw [ih]
    congr 1
    exact map_action f x y s j

theorem transported (f : G→*H) (x y : G) (w : Array P) (tab : Array Q)
    (c : H) (cx : Commute c (f x)) (cy : Commute c (f y))
    (xy : f x*f y=f y*f x*c) (h0 : tab[0]! = (false,0,0,0))
    (hstep : ∀ i, i<w.size → push tab[i]! w[i]! = tab[i+1]!) :
    ∀ i, i≤w.size → (fun u : Bool × G => (u.1,f u.2)) (pathAt x y w i) =
      vert (f x) (f y) c tab[i]! := by
  intro i
  induction i with
  | zero =>
     intro _
     simp [pathAt,run,start,vert,h0,HaarCycle.norm]
  | succ i ih =>
     intro hi
     have Hi : i<w.size := by omega
     have e := ih (by omega : i≤w.size)
     change ((pathAt x y w i).1, f (pathAt x y w i).2) = vert (f x) (f y) c tab[i]! at e
     rw [pathAt_next x y w Hi,map_action,e]
     rw [← hstep i Hi,move (f x) (f y) c cx cy xy]

theorem cycle_from_at {n : Nat} (x y : G) (w : Array P) (len : w.size=n)
    (close : pathAt x y w n=pathAt x y w 0)
    (no : ∀ i j : Fin n, i.val<j.val → pathAt x y w i.val≠pathAt x y w j.val) :
    Ribbon.Cycle x y n := by
  refine ⟨fun i => pathAt x y w i.val,?_,?_⟩
  · intro i j e
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with L|L
    · exact (no i j L) e
    · exact (no j i L) e.symm
  · intro i
    have H := action_adj x y (pathAt x y w i.val) w[i.val]!
    rw [← pathAt_next x y w (i:=i.val) (by rw [len]; exact i.isLt)] at H
    by_cases hs : i.val+1<n
    · simpa [Nat.mod_eq_of_lt hs] using H
    · have e : i.val+1=n := by have h := i.isLt; omega
      simpa [e,Nat.mod_self,close] using H

end Ribbon5Bridge
#print axioms Ribbon5Bridge.transported
#print axioms Ribbon5Bridge.cycle_from_at
