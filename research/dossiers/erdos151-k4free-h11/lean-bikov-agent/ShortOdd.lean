import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace BikovLocal
variable {V : Type*}

structure Walk (R : V→V→Prop) (u v : V) where
  len : Nat
  atV : Nat→V
  first : atV 0=u
  last : atV len=v
  step : ∀ i, i<len → R (atV i) (atV (i+1))

namespace Walk
variable {R : V→V→Prop} {x y z : V}

def nil (R : V→V→Prop) (x : V) : Walk R x x :=
  ⟨0,fun _=>x,rfl,rfl,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩

def single (h : R x y) : Walk R x y := by
  refine ⟨1,fun i=>if i=0 then x else y,by simp,by simp,?_⟩
  intro i hi
  have he : i=0 := by omega
  simpa [he] using h

def append (p : Walk R x y) (q : Walk R y z) : Walk R x z := by
  refine ⟨p.len+q.len,fun i=>if i<p.len then p.atV i else q.atV (i-p.len),?_,?_,?_⟩
  · by_cases h : 0<p.len
    · simp [h,p.first]
    · have hp : p.len=0 := by omega
      simp [h,q.first,←p.last,hp,p.first]
  · have h : ¬p.len+q.len<p.len := by omega
    simp [h,q.last]
  · intro i hi
    by_cases h : i<p.len
    · by_cases h' : i+1<p.len
      · simp only [if_pos h,if_pos h']
        exact p.step i h
      · have e : i+1=p.len := by omega
        simpa only [if_pos h,if_neg h',e,Nat.lt_irrefl,ite_false,Nat.sub_self,q.first,p.last] using p.step i h
    · have h' : ¬ i+1<p.len := by omega
      simp only [if_neg h,if_neg h']
      have e : i+1-p.len=(i-p.len)+1 := by omega
      rw [e]
      exact q.step _ (by omega)

def reverse (sym : ∀ ⦃a b⦄, R a b → R b a) (p : Walk R x y) : Walk R y x := by
  refine ⟨p.len,fun i=>p.atV (p.len-i),by rw [Nat.sub_zero,p.last],by rw [Nat.sub_self,p.first],?_⟩
  intro i h
  have eq : p.len-(i+1)+1=p.len-i := by omega
  apply sym
  rw [←eq]
  exact p.step _ (by omega)

def slice (p : Walk R x y) (i j : Nat) (ij : i≤j) (jl : j≤p.len) :
    Walk R (p.atV i) (p.atV j) := by
  refine ⟨j-i,fun k=>p.atV (i+k),by simp,?_,?_⟩
  · congr 1
    omega
  · intro k h
    exact p.step (i+k) (by omega)

def cast (p : Walk R x y) {a b : V} (hx : x=a) (hy : y=b) : Walk R a b :=
  ⟨p.len,p.atV,p.first.trans hx,p.last.trans hy,p.step⟩

end Walk

/-- Absence of an odd closed walk yields an actual two-coloring of vertices. -/
theorem bipartition_of_no_odd (R : V→V→Prop)
    (sym : ∀ ⦃a b⦄, R a b → R b a)
    (no : ¬∃ x, ∃ p : Walk R x x, p.len % 2=1) :
    ∃ f : V→Bool, ∀ ⦃x y⦄, R x y → f x≠f y := by
  classical
  let S : Setoid V := ⟨fun x y=>Nonempty (Walk R x y),
    fun x=>⟨Walk.nil R x⟩,
    fun ⟨p⟩=>⟨p.reverse sym⟩,
    fun ⟨p⟩ ⟨q⟩=>⟨p.append q⟩⟩
  let q (x : V) : Quotient S := Quotient.mk S x
  let root (x : V) := (q x).out
  have reaches (x : V) : Nonempty (Walk R (root x) x) := by
    exact Quotient.exact (s:=S) (Quotient.out_eq (q x))
  let p (x : V) := Classical.choice (reaches x)
  let f (x : V) : Bool := decide ((p x).len % 2=1)
  refine ⟨f,?_⟩
  intro x y e s
  have rot : root x=root y := congrArg Quotient.out
    (Quotient.sound (s:=S) (show Nonempty (Walk R x y) from ⟨Walk.single e⟩))
  let w := ((p x).append (Walk.single e)).append ((p y).reverse sym |>.cast rfl rot.symm)
  apply no
  refine ⟨root x,w,?_⟩
  have same : ((p x).len % 2=1) ↔ ((p y).len % 2=1) := by
    simpa only [f,decide_eq_decide] using s
  change ((p x).len+1+(p y).len) % 2=1
  omega

/-- A globally shortest odd closed walk has no repeated vertex before the
closing step and no chords. The length alternatives remain explicit. -/
theorem shortest_odd (R : V→V→Prop)
    (sym : ∀ ⦃a b⦄, R a b → R b a)
    (odd : ∃ x, ∃ p : Walk R x x, p.len % 2=1) :
    ∃ x, ∃ p : Walk R x x, p.len % 2=1 ∧
      (∀ i j, i<j → j<p.len → p.atV i≠p.atV j) ∧
      (∀ i j, i+1<j → j<p.len → (i≠0 ∨ j+1<p.len) →
        ¬ R (p.atV i) (p.atV j)) := by
  classical
  have E : ∃ n, ∃ x, ∃ p : Walk R x x, p.len=n ∧ p.len % 2=1 := by
    obtain ⟨x,p,h⟩ := odd
    exact ⟨p.len,x,p,rfl,h⟩
  obtain ⟨x,p,l,h⟩ := Nat.find_spec E
  have forbid (u : V) (q : Walk R u u) (s : q.len<p.len) (b : q.len%2=1) : False := by
    have m := Nat.find_min' E (show ∃ x, ∃ p : Walk R x x, p.len=q.len ∧ p.len%2=1 from ⟨u,q,rfl,b⟩)
    omega
  refine ⟨x,p,h,?_,?_⟩
  · intro i j ij lj rep
    let q := (p.slice i j (by omega) (by omega)).cast rfl rep.symm
    let a := (p.slice j p.len (by omega) (by omega)).cast rep.symm p.last
    let b := (p.slice 0 i (by omega) (by omega)).cast p.first rfl
    let r := a.append b
    have lq : q.len=j-i := rfl
    have lr : r.len=p.len-j+i := by change p.len-j+(i-0)=_; omega
    by_cases o : q.len%2=1
    · exact forbid _ q (by omega) o
    · exact forbid _ r (by omega) (by omega)
  · intro i j ij lj wrap e
    let q := (p.slice i j (by omega) (by omega)).append (Walk.single (sym e))
    let a := (p.slice j p.len (by omega) (by omega)).cast rfl p.last
    let b := (p.slice 0 i (by omega) (by omega)).cast p.first rfl
    let r := (Walk.single e).append (a.append b)
    have lq : q.len=j-i+1 := rfl
    have lr : r.len=1+(p.len-j+i) := by change 1+(p.len-j+(i-0))=_; omega
    by_cases o : q.len%2=1
    · exact forbid _ q (by omega) o
    · exact forbid _ r (by omega) (by omega)

#print axioms bipartition_of_no_odd
#print axioms shortest_odd
end BikovLocal
