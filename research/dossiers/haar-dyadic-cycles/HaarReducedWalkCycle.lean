import HaarHalfCollision

namespace HaarReducedWalkCycle
open HaarCycle HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem extract (x y : G) (N : ℕ) (a : ℕ → Bool × G)
    (n4 : 4 ≤ N) (closed : a N=a 0)
    (edges : ∀ i<N, haarAdj x y (a i) (a (i+1)))
    (side : ∀ i≤N, (a i).1=decide (i%2=1))
    (noBounce : ∀ i, i+2≤N → a (i+2)≠a i) :
    ∃ k, 4≤k ∧ k≤N ∧ Even k ∧ HasCycle x y k := by
  classical
  let repeatAt (k : ℕ) := ∃ i : ℕ, 0<k ∧ i+k≤N ∧ a (i+k)=a i
  have e : ∃ k, repeatAt k := ⟨N,0,by simpa using And.intro (show 0<N by omega) (And.intro (le_refl N) closed)⟩
  have existsMin : ∃ k, repeatAt k ∧ ∀ q<k, ¬ repeatAt q :=
    ⟨Nat.find e,Nat.find_spec e,fun _ h => Nat.find_min e h⟩
  obtain ⟨k,⟨i,hpos,hN,hen⟩,kno⟩ := existsMin
  have parity : k%2=0 := by
    have hp := congrArg Prod.fst hen
    rw [side _ hN, side _ (by omega)] at hp
    by_contra h
    have u : k%2=1 := by omega
    by_cases z : i%2=1
    · have w : (i+k)%2≠1 := by omega
      simp [z,w] at hp
    · have w : (i+k)%2=1 := by omega
      simp [z,w] at hp
  have n2 : k≠2 := by
    intro h
    exact noBounce i (by omega) (by simpa [h] using hen)
  have h4 : 4≤k := by omega
  refine ⟨k,h4,by omega,⟨k/2,by omega⟩,?_,?_⟩
  · exact fun j => a (i+j.val)
  · constructor
    · intro j l eq
      apply Fin.ext
      by_contra he
      rcases lt_or_gt_of_ne he with lt|lt
      · apply kno (l.val-j.val) (by omega)
        refine ⟨i+j.val,by omega,by omega,?_⟩
        rw [show i+j.val+(l.val-j.val)=i+l.val by omega]
        exact eq.symm
      · apply kno (j.val-l.val) (by omega)
        refine ⟨i+l.val,by omega,by omega,?_⟩
        rw [show i+l.val+(j.val-l.val)=i+j.val by omega]
        exact eq
    · intro j
      change haarAdj x y (a (i+j.val)) (a (i+(j.val+1)%k))
      have h := edges (i+j.val) (by omega)
      by_cases hj : j.val+1<k
      · rw [Nat.mod_eq_of_lt hj,←Nat.add_assoc]; exact h
      · have jE : j.val+1=k := by omega
        rw [jE,Nat.mod_self,Nat.add_zero,←hen]
        rwa [Nat.add_assoc,jE] at h

open HaarHalfCollision
def label (w : List (Fin 3)) (i : ℕ) := w[i]?.getD 0

theorem segment_label (w : List (Fin 3)) :
    HaarSharpGraph.segment (label w) 0 w.length=w := by
  have shift (c : ℕ → Fin 3) (j n : ℕ) :
      HaarSharpGraph.segment c (j+1) n = HaarSharpGraph.segment (fun i => c (i+1)) j n := by
    induction n generalizing j with
    | zero => rfl
    | succ n ih =>
      simpa only [HaarSharpGraph.segment,HaarSharpGraph.segment] using
        congrArg (c (j+1)::·) (ih (j+1))
  induction w with
  | nil => rfl
  | cons c w ih =>
    change c :: HaarSharpGraph.segment (label (c::w)) 1 w.length = c::w
    rw [show 1=0+1 by rfl,shift]
    exact congrArg (c::·) ih

theorem good_adj (w : List (Fin 3)) (g : HaarSharpCore.good w=true) (i : ℕ)
    (hi : i+2≤w.length) : label w i ≠ label w (i+1) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons c w ih =>
    cases w with
    | nil => simp at hi
    | cons d t =>
      change ((c != d) && HaarSharpCore.good (d::t))=true at g
      simp only [Bool.and_eq_true] at g
      cases i with
      | zero =>
        intro q
        have e : c=d := q
        simp [e] at g
      | succ i =>
        exact ih g.2 i (by simpa using show i+2≤(d::t).length by simp at hi ⊢; omega)

def path (x y : G) (w : List (Fin 3)) : ℕ → G
  | 0 => 1
  | i+1 => path x y w i * signPort x y i (label w i)

theorem port_inj (x y : G) (u : x≠1) (v : y≠1) (w : x≠y) :
    Function.Injective (port x y) := by
  intro i j e
  fin_cases i <;> fin_cases j <;> simp_all [port]

theorem fromWord (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (w : List (Fin 3)) (n4 : 4≤w.length) (even : Even w.length) (g : HaarSharpCore.good w=true)
    (closed : prodFrom x y 0 w=1) :
    ∃ k, 4≤k ∧ k≤w.length ∧ Even k ∧ HasCycle x y k := by
  let a (i : ℕ) : Bool × G := (decide (i%2=1),path x y w i)
  apply extract x y w.length a n4
  · have p := segment_product x y (path x y w) (label w) 0 0 w.length (by intro; intros; simp only [Nat.zero_add,path])
    have ev : path x y w w.length=1 := by simpa [path,segment_label,closed] using p
    have parity : w.length%2=0 := by
      obtain ⟨j,hj⟩ := even
      omega
    simp [a,path,ev,parity]
  · intro i _
    have f : (i+1)%2=1 ↔ i%2=0 := by omega
    have h : (i+1)%2=0 ↔ i%2=1 := by omega
    have h3 (c : Fin 3) : port x y c=1 ∨ port x y c=x ∨ port x y c=y := by
      fin_cases c <;> simp [port]
    obtain q|q|q := h3 (label w i) <;>
      (by_cases ev : i%2=0
       · have o := f.mpr ev
         have no : i%2≠1 := by omega
         simp [haarAdj,a,path,signPort,ev,o,q]
       · have o : i%2=1 := by omega
         have np : (i+1)%2≠1 := by omega
         simp [haarAdj,a,path,signPort,o,np,q,mul_assoc])
  · intro i _; rfl
  · intro i hi eq
    have ee := congrArg Prod.snd eq
    change path x y w (i+2)=path x y w i at ee
    simp only [path,mul_assoc] at ee
    have et : signPort x y i (label w i) * signPort x y (i+1) (label w (i+1))=1 :=
      mul_left_cancel (ee.trans (mul_one _).symm)
    have eql : port x y (label w i)=port x y (label w (i+1)) := by
      by_cases ev : i%2=0
      · have np : (i+1)%2≠0 := by omega
        simpa [signPort,ev,np,mul_inv_eq_one] using et
      · have np : (i+1)%2=0 := by omega
        simpa [signPort,ev,np,inv_mul_eq_one] using et
    exact good_adj w g i hi (port_inj x y hx hy hxy eql)

end HaarReducedWalkCycle
#print axioms HaarReducedWalkCycle.extract
#print axioms HaarReducedWalkCycle.fromWord
