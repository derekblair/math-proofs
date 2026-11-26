import GenericVoltage
import Mathlib.Tactic

namespace ShortProjection
open GenericVoltage

variable {V : Type*} {R : V → V → Prop}

theorem cycle_in_segment (a : ℕ→V)
    (E : ∀ i, R (a i) (a (i+1))) (sep1 : ∀ i, a i≠a (i+1))
    (sep2 : ∀ i, a i≠a (i+2))
    {l r : ℕ} (lr : l<r) (closed : a l=a r) :
    ∃ n, 3≤n ∧ n≤r-l ∧ Cycle R n := by
  classical
  let good (δ : ℕ) := 0 < δ ∧ ∃ i, l ≤ i ∧ i+δ ≤ r ∧ a i=a (i+δ)
  have existsGood : ∃ δ, good δ := by
    refine ⟨r-l,by omega,l,le_rfl,by omega,?_⟩
    have eq : l+(r-l)=r := by omega
    rw [eq]; exact closed
  let n := Nat.find existsGood
  obtain ⟨np,i,li,ir,both⟩ := Nat.find_spec existsGood
  change a i = a (i+n) at both
  have n3 : 3≤n := by
    by_contra! pre
    have Z : n=1 ∨ n=2 := by omega
    rcases Z with ep|ep
    · exact sep1 i (by simpa only [ep] using both)
    · exact sep2 i (by simpa only [ep] using both)
  refine ⟨n,n3,by omega,fun q => a (i+q.val),?_,?_⟩
  · intro u v h
    apply Fin.ext
    by_cases hsame : u.val=v.val
    · exact hsame
    · have bad (x y : Fin n) (lt : x.val<y.val) (eq : a (i+x.val)=a (i+y.val)) : False := by
        have D : good (y.val-x.val) := by
          refine ⟨by omega,i+x.val,by omega,by omega,?_⟩
          have H : i+x.val+(y.val-x.val)=i+y.val := by omega
          simpa only [H] using eq
        have nb : n≤y.val-x.val := Nat.find_min' existsGood D
        have hy := y.isLt
        omega
      exact False.elim (if H : u.val<v.val then bad u v H h else bad v u (by omega) h.symm)
  · intro u
    by_cases H : u.val+1<n
    · simpa only [Nat.mod_eq_of_lt H,Nat.add_assoc] using E (i+u.val)
    · have eq : u.val+1=n := by omega
      have step := E (i+u.val)
      rw [Nat.add_assoc,eq,←both] at step
      simpa only [eq,Nat.mod_self,Nat.add_zero] using step

/-- A closed reduced walk shorter than twice the base girth has no internal
repeated vertex. A repeated vertex would split it into two closed reduced
segments, each containing a simple cycle. -/
theorem no_repeat (a : ℕ→V) (n g : ℕ)
    (E : ∀ i, R (a i) (a (i+1))) (sep1 : ∀ i, a i≠a (i+1))
    (sep2 : ∀ i, a i≠a (i+2)) (per : ∀ i, a (i+n)=a i)
    (girth : ∀ k, 3≤k → Cycle R k → g≤k)
    (short : n<2*g) : Function.Injective (fun i : Fin n => a i.val) := by
  intro u v h
  apply Fin.ext
  have kill (x y : Fin n) (hlt : x.val<y.val) (eq : a x.val=a y.val) : False := by
    obtain ⟨l,hl,L,cl⟩ := cycle_in_segment a E sep1 sep2 hlt eq
    have returned : a y.val=a (x.val+n) := eq.symm.trans (per x.val).symm
    have rpos : y.val<x.val+n := by have hy := y.isLt; omega
    obtain ⟨r,hr,Rc,cr⟩ := cycle_in_segment a E sep1 sep2 rpos returned
    have gl := girth l hl cl
    have gr := girth r hr cr
    omega
  by_contra H
  exact if lt : u.val<v.val then kill u v lt h else kill v u (by omega) h.symm

theorem cover_projection {U : Type*} (T : U→U→Prop) (π : U→V)
    (symm : ∀ {x y}, T x y → T y x) (map : ∀ {x y}, T x y → R (π x) (π y))
    (localInj : ∀ {x y z}, T x y → T x z → π y=π z → y=z)
    (loopless : ∀ x, ¬R x x) {g n : ℕ} (hn : 3≤n) (short : n<2*g)
    (girth : ∀ k, 3≤k → Cycle R k → g≤k) (c : Cycle T n) :
    Cycle R n := by
  obtain ⟨f,fi,fe⟩ := c
  let I (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt _ (by omega)⟩
  let p (i : ℕ) := f (I i)
  let a (i : ℕ) := π (p i)
  have edge (i : ℕ) : T (p i) (p (i+1)) := by
    have F := fe (I i)
    have J : (⟨((I i).val+1)%n,Nat.mod_lt _ (by omega)⟩ : Fin n)=I (i+1) := by
      apply Fin.ext
      change ((i%n)+1)%n=(i+1)%n
      rw [Nat.add_mod (i%n),Nat.mod_mod,Nat.add_mod i]
    rw [J] at F
    exact F
  have E : ∀ i, R (a i) (a (i+1)) := fun i => map (edge i)
  have sep1 (i : ℕ) : a i≠a (i+1) := fun eq => loopless _ (eq ▸ E i)
  have sep2 (i : ℕ) : a i≠a (i+2) := by
    intro eq
    have h : p i=p (i+2) := localInj (symm (edge i)) (edge (i+1)) eq
    have mod : (i+2)%n=i%n := (congrArg Fin.val (fi h)).symm
    have n2 : 2<n := by omega
    have d := Nat.add_mod i 2 n
    rw [Nat.mod_eq_of_lt n2,mod] at d
    have nn : (i%n)<n := Nat.mod_lt _ (by omega)
    by_cases B : i%n+2<n
    · rw [Nat.mod_eq_of_lt B] at d
      omega
    · have s : (i%n+2)%n=i%n+2-n := Nat.mod_eq_sub_mod (by omega) |>.trans
        (Nat.mod_eq_of_lt (by omega))
      rw [s] at d
      omega
  have per (i : ℕ) : a (i+n)=a i := by
    have J : I (i+n)=I i := Fin.ext (Nat.add_mod_right i n)
    exact congrArg (fun j => π (f j)) J
  have ai := no_repeat a n g E sep1 sep2 per girth short
  have id (i : Fin n) : I i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  refine ⟨π ∘ f, ?_, fun i => map (fe i)⟩
  intro i j eq
  apply ai
  change π (f (I i.val))=π (f (I j.val))
  simpa only [id,Function.comp_apply] using eq

end ShortProjection
#print axioms ShortProjection.cycle_in_segment
#print axioms ShortProjection.no_repeat
#print axioms ShortProjection.cover_projection
