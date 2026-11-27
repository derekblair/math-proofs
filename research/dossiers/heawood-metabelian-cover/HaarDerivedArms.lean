import HaarDerivedFlowPositive
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card

namespace HaarDerivedArms
open HaarDerivedFlowPositive
variable {V : Type*} (R : V → V → Prop)

theorem cycle_of_closed (a : Nat → V) (N : Nat) (N0 : 0<N)
    (close : a N=a 0) (edge : ∀ i<N, R (a i) (a (i+1)))
    (loop : ∀ a, ¬R a a) (nb : ∀ i, i+2≤N → a (i+2)≠a i) :
    ∃ k, 3≤k ∧ k≤N ∧ Cyclic R k := by
  classical
  let P (k : Nat) := 0<k ∧ ∃ i, i+k≤N ∧ a (i+k)=a i
  have ex : ∃ k, P k := ⟨N,N0,0,by simpa using (show N≤N from le_rfl),by simpa using close⟩
  let k := Nat.find ex
  obtain ⟨kp,i,ki,eq⟩ := Nat.find_spec ex
  change a (i+k)=a i at eq
  change 0<k at kp
  change i+k≤N at ki
  have min (b c : Nat) (bc : b<c) (cN : c≤N) (e : a b=a c) : k≤c-b :=
    Nat.find_min' ex ⟨by omega,b,by omega,by rw [show b+(c-b)=c by omega]; exact e.symm⟩
  have ge3 : 3≤k := by
    by_contra C
    have d : k=1 ∨ k=2 := by omega
    rcases d with d|d
    · rw [d] at eq
      have J := edge i (by omega)
      rw [eq] at J
      exact loop _ J
    · rw [d] at eq
      exact nb i (by omega) eq
  refine ⟨k,ge3,by omega,fun j => a (i+j.val),?_,?_⟩
  · intro a b d
    apply Fin.ext
    rcases lt_trichotomy a.val b.val with h|h|h
    · have j := min (i+a.val) (i+b.val) (by omega) (by omega) d
      omega
    · exact h
    · have j := min (i+b.val) (i+a.val) (by omega) (by omega) d.symm
      omega
  · intro j
    have h := edge (i+j.val) (by omega)
    by_cases e : j.val+1<k
    · simpa only [Nat.mod_eq_of_lt e,Nat.add_assoc] using h
    · have he : j.val+1=k := by omega
      have HH : i+j.val+1=i+k := by omega
      simpa only [HH,eq,he,Nat.mod_self,Nat.add_zero] using h

theorem no_short_repeat (a : Nat → V) (h : Nat)
    (girth : ∀ n, 3≤n → Cyclic R n → 2*h≤n)
    (loop : ∀ a, ¬R a a) (walk : ∀ i<h, R (a i) (a (i+1)))
    (nb : ∀ i, i+2≤h → a (i+2)≠a i) :
    ∀ i j, i≤h → j≤h → a i=a j → i=j := by
  have strict (i j : Nat) (hi : j≤h) (ij : i<j) (e : a i=a j) : False := by
    obtain ⟨k,k3,klen,C⟩ := cycle_of_closed R (fun l => a (i+l)) (j-i) (by omega)
      (by rw [show i+(j-i)=j by omega,Nat.add_zero]; exact e.symm)
      (by intro l lt; simpa only [Nat.add_assoc] using walk (i+l) (by omega)) loop
      (by intro l hl; simpa only [Nat.add_assoc] using nb (i+l) (by omega))
    have kmin := girth k k3 C
    omega
  intro i j ih jh e
  rcases lt_trichotomy i j with q|q|q
  · exact (strict i j jh q e).elim
  · exact q
  · exact (strict j i ih q e.symm).elim

theorem arms_meet (A B : Nat → V) (h : Nat)
    (girth : ∀ n, 3≤n → Cyclic R n → 2*h≤n)
    (loop : ∀ a, ¬R a a) (symm : ∀ {a b}, R a b → R b a)
    (start : A 0=B 0) (first : A 1≠B 1)
    (EA : ∀ i<h, R (A i) (A (i+1))) (EB : ∀ i<h, R (B i) (B (i+1)))
    (NA : ∀ i, i+2≤h → A (i+2)≠A i) (NB : ∀ i, i+2≤h → B (i+2)≠B i) :
    ∀ i j, 0<i → i≤h → 0<j → j≤h → A i=B j → i=h ∧ j=h := by
  classical
  intro i j i0 ih j0 jh e
  let P (n : Nat) := ∃ a b, 0<a ∧ a≤h ∧ 0<b ∧ b≤h ∧ a+b=n ∧ A a=B b
  have ex : ∃ n, P n := ⟨i+j,i,j,i0,ih,j0,jh,rfl,e⟩
  let n := Nat.find ex
  obtain ⟨a,b,a0,ah,b0,bh,ab,inter⟩ := Nat.find_spec ex
  have min : n≤i+j := Nat.find_min' ex ⟨i,j,i0,ih,j0,jh,rfl,e⟩
  have not11 : ¬ (a=1 ∧ b=1) := by rintro ⟨rfl,rfl⟩; exact first inter
  have mid : A (a-1)≠ B (b-1) := by
    intro eq
    by_cases at0 : a=1
    · have eb : B (b-1)=B 0 := by simpa [at0,start] using eq.symm
      have Z := no_short_repeat R B h girth loop EB NB (b-1) 0 (by omega) (by omega) eb
      exact not11 ⟨at0,by omega⟩
    by_cases bt0 : b=1
    · have ea : A (a-1)=A 0 := by simpa [bt0,←start] using eq
      have Z := no_short_repeat R A h girth loop EA NA (a-1) 0 (by omega) (by omega) ea
      exact not11 ⟨by omega,bt0⟩
    have bad : n≤a-1+(b-1) := Nat.find_min' ex
      ⟨a-1,b-1,by omega,by omega,by omega,by omega,rfl,eq⟩
    omega
  let c (l : Nat) := if l≤a then A l else B (a+b-l)
  have edge (l : Nat) (hl : l<a+b) : R (c l) (c (l+1)) := by
    by_cases a1 : l+1≤a
    · simp only [c,if_pos a1,if_pos (show l≤a by omega)]
      exact EA l (by omega)
    by_cases la : l≤a
    · have z : l=a := by omega
      subst l
      simp only [c,if_pos le_rfl,if_neg a1,inter]
      have id : a+b-(a+1)+1=b := by omega
      apply symm
      have H := EB (a+b-(a+1)) (by omega)
      rwa [id] at H
    · simp only [c,if_neg a1,if_neg la]
      apply symm
      have id : a+b-(l+1)+1=a+b-l := by omega
      have H := EB (a+b-(l+1)) (by omega)
      rwa [id] at H
  have nb (l : Nat) (hl : l+2≤a+b) : c (l+2)≠c l := by
    by_cases sa : l+2≤a
    · simp only [c,if_pos sa,if_pos (show l≤a by omega)]
      exact NA l (by omega)
    by_cases al : a≤l
    · have c1 : c l=B (a+b-l) := by
        by_cases eq : l=a
        · subst l
          simpa only [c,if_pos le_rfl,show a+b-a=b by omega] using inter
        · simp [c,show ¬l≤a by omega]
      rw [c1]
      simp only [c,if_neg sa]
      have id : a+b-(l+2)+2=a+b-l := by omega
      have H := NB (a+b-(l+2)) (by omega)
      rw [id] at H
      exact H.symm
    · have E : l+1=a := by omega
      have L : l=a-1 := by omega
      have Q : a+b-(l+2)=b-1 := by omega
      simp only [c,if_neg sa,if_pos (show l≤a by omega)]
      rw [Q,L]
      exact mid.symm
  have closed : c (a+b)=c 0 := by simp [c,show ¬a+b≤a by omega,start]
  obtain ⟨k,k3,kN,C⟩ := cycle_of_closed R c (a+b) (by omega) closed edge loop nb
  have gmin := girth k k3 C
  omega

open scoped Sym2 in
theorem count_arms [DecidableEq V] (h : Nat)
    (girth : ∀ n, 3≤n → Cyclic R n → 2*h≤n)
    (loop : ∀ a, ¬R a a) (symm : ∀ {a b}, R a b → R b a)
    (E : Finset (Sym2 V)) (u : V) (A : Fin 3 → Nat → V)
    (base : ∀ t, A t 0=u) (first : Function.Injective (fun t => A t 1))
    (walk : ∀ t i, i<h → R (A t i) (A t (i+1)))
    (nb : ∀ t i, i+2≤h → A t (i+2)≠A t i)
    (mem : ∀ t i, i<h → s(A t i,A t (i+1))∈E) :
    3*h≤E.card := by
  classical
  let f (v : Fin 3 × Fin h) : Sym2 V := s(A v.1 v.2.val,A v.1 (v.2.val+1))
  have same (t : Fin 3) (i j : Nat) (ih : i≤h) (jh : j≤h) (e : A t i=A t j) : i=j :=
    no_short_repeat R (A t) h girth loop (walk t) (nb t) i j ih jh e
  have cross (s t : Fin 3) (ne : s≠t) (i j : Nat) (i0 : 0<i) (ih : i≤h)
      (j0 : 0<j) (jh : j≤h) (e : A s i=A t j) : i=h ∧ j=h :=
    arms_meet R (A s) (A t) h girth loop symm (by rw [base,base])
      (fun z => ne (first z)) (walk s) (walk t) (nb s) (nb t) i j i0 ih j0 jh e
  have fi : Function.Injective f := by
    rintro ⟨s,i⟩ ⟨t,j⟩ e
    change s(A s i.val,A s (i.val+1))=s(A t j.val,A t (j.val+1)) at e
    have hi := i.isLt
    have hj := j.isLt
    rcases Sym2.eq_iff.mp e with ⟨x,y⟩|⟨x,y⟩
    · by_cases st : s=t
      · subst t
        exact Prod.ext rfl (Fin.ext (same s _ _ (by omega) (by omega) x))
      · by_cases iz : i.val=0
        · have J : A t j.val=A t 0 := by simpa only [iz,base] using x.symm
          have jz := same t j.val 0 (by omega) (by omega) J
          exact False.elim (st (first (by simpa only [iz,jz,Nat.zero_add] using y)))
        by_cases jz : j.val=0
        · have I : A s i.val=A s 0 := by simpa only [jz,base] using x
          exact False.elim (iz (same s i.val 0 (by omega) (by omega) I))
        have Z := cross s t st i.val j.val (by omega) (by omega) (by omega) (by omega) x
        omega
    · by_cases st : s=t
      · subst t
        have X := same s i.val (j.val+1) (by omega) (by omega) x
        have Y := same s (i.val+1) j.val (by omega) (by omega) y
        omega
      · by_cases iz : i.val=0
        · have J : A t (j.val+1)=A t 0 := by simpa only [iz,base] using x.symm
          have Z := same t (j.val+1) 0 (by omega) (by omega) J
          omega
        have Z := cross s t st i.val (j.val+1) (by omega) (by omega) (by omega) (by omega) x
        omega
  let T : Finset (Sym2 V) := Finset.univ.map ⟨f,fi⟩
  have sub : T ⊆ E := by
    intro e he
    obtain ⟨⟨t,i⟩,_,rfl⟩ := Finset.mem_map.mp he
    exact mem t i.val i.isLt
  have H := Finset.card_le_card sub
  simpa [T] using H

end HaarDerivedArms
#print axioms HaarDerivedArms.arms_meet
#print axioms HaarDerivedArms.count_arms
