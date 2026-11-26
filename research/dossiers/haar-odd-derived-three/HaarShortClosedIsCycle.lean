import HaarReducedWalkCycle
import HaarVoltage

namespace HaarShortClosedIsCycle
open HaarCycle HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem extract_short (x y : G) (N : ℕ) (a : ℕ → Bool × G)
    (n0 : 0 < N) (closed : a N=a 0)
    (edges : ∀ i<N, haarAdj x y (a i) (a (i+1)))
    (side : ∀ i j, i+j≤N → a (i+j)=a i → j%2=0)
    (noBounce : ∀ i, i+2≤N → a (i+2)≠a i) :
    ∃ k, 4≤k ∧ k≤N ∧ Even k ∧ HasCycle x y k := by
  classical
  let repeatAt (k : ℕ) := ∃ i : ℕ, 0<k ∧ i+k≤N ∧ a (i+k)=a i
  have e : ∃ k, repeatAt k := ⟨N,0,by simpa using And.intro (show 0<N by omega) (And.intro (le_refl N) closed)⟩
  have existsMin : ∃ k, repeatAt k ∧ ∀ q<k, ¬ repeatAt q :=
    ⟨Nat.find e,Nat.find_spec e,fun _ h => Nat.find_min e h⟩
  obtain ⟨k,⟨i,hpos,hN,hen⟩,kno⟩ := existsMin
  have parity := side i k hN hen
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

omit [Group G] in
theorem parity_return (a : ℕ → Bool × G)
    (flip : ∀ i, (a (i+1)).1 = !(a i).1) (i j : ℕ) (e : a (i+j)=a i) : j%2=0 := by
  have H (k : ℕ) : (a (i+k)).1 = if k%2=0 then (a i).1 else !(a i).1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [←Nat.add_assoc,flip,ih]
      by_cases z : k%2=0
      · have z1 : (k+1)%2≠0 := by omega
        simp [z,z1]
      · have z1 : (k+1)%2=0 := by omega
        simp [z,z1]
  have f := congrArg Prod.fst e
  rw [H] at f
  by_contra hn
  cases u : (a i).1 <;> simp [u,hn] at f

theorem periodic_simple (x y : G) (N g : ℕ) (a : ℕ → Bool × G)
    (n4 : 4≤N) (ng : N<2*g)
    (period : ∀ i, a (i+N)=a i)
    (edges : ∀ i, haarAdj x y (a i) (a (i+1)))
    (bounce : ∀ i, a (i+2)≠a i)
    (noShort : ∀ k, 4≤k → k<g → Even k → ¬HasCycle x y k) :
    HasCycle x y N := by
  have too_short (t d : ℕ) (d0 : 0<d) (dg : d<g)
      (e : a (t+d)=a t) : False := by
    let b (i : ℕ) := a (t+i)
    have bz : b d=b 0 := by simpa [b] using e
    have be (i : ℕ) (_ : i<d) : haarAdj x y (b i) (b (i+1)) := by
      simpa [b,Nat.add_assoc] using edges (t+i)
    have nr (i j : ℕ) (_ : i+j≤d) (e : b (i+j)=b i) : j%2=0 := by
      have f (i : ℕ) := (HaarHalfCollision.branch x y _ _ (edges i)).1
      exact parity_return a f (t+i) j (by simpa [b,Nat.add_assoc] using e)
    have bn (i : ℕ) (_ : i+2≤d) : b (i+2)≠b i := by
      simpa [b,Nat.add_assoc] using bounce (t+i)
    obtain ⟨k,k4,kd,ke,kc⟩ := extract_short x y d b d0 bz be nr bn
    exact noShort k k4 (by omega) ke kc
  have inj_aux (i j : ℕ) (ij : i<j) (jN : j<N) (e : a i=a j) : False := by
    let d := j-i
    have d0 : 0<d := by dsimp [d]; omega
    by_cases dg : d<g
    · exact too_short i d d0 dg (by rw [show i+d=j by dsimp [d]; omega]; exact e.symm)
    · have dg' : N-d<g := by omega
      have eq : j+(N-d)=i+N := by dsimp [d]; omega
      apply too_short j (N-d) (by dsimp [d]; omega) dg'
      rw [eq,period i,e]
  refine ⟨fun i => a i.val,?_,?_⟩
  · intro i j eq
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h|h
    · exact inj_aux _ _ h j.isLt eq
    · exact inj_aux _ _ h i.isLt eq.symm
  · intro i
    change haarAdj x y (a i.val) (a ((i.val+1)%N))
    by_cases h : i.val+1<N
    · rw [Nat.mod_eq_of_lt h]
      exact edges i.val
    · have hN : i.val+1=N := by omega
      have e := edges i.val
      have z : a N=a 0 := by simpa using period 0
      rw [hN,Nat.mod_self]
      rwa [hN,z] at e


open HaarHalfCollision HaarReducedWalkCycle HaarVoltage

theorem cyclic_labels (w : List (Fin 3)) (n4 : 4≤w.length)
    (g : HaarSharpCore.good w=true) (last : label w (w.length-1) ≠ label w 0) (i : ℕ) :
    label w (i%w.length) ≠ label w ((i+1)%w.length) := by
  let n := w.length
  have np : 0<n := by omega
  have t : i%n<n := Nat.mod_lt _ np
  have e : (i+1)%n = (i%n+1)%n := by
    have e := Nat.add_mod i 1 n
    simpa only [Nat.mod_eq_of_lt (show 1<n by omega)] using e
  change label w (i%n) ≠ label w ((i+1)%n)
  rw [e]
  by_cases h : i%n+1<n
  · rw [Nat.mod_eq_of_lt h]
    exact good_adj w g _ (by omega)
  · have eq : i%n+1=n := by omega
    rw [eq,Nat.mod_self,show i%n=n-1 by omega]
    exact last

theorem fromWord (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (w : List (Fin 3)) (n4 : 4≤w.length) (even : Even w.length)
    (good : HaarSharpCore.good w=true) (closed : prodFrom x y 0 w=1)
    (last : label w (w.length-1) ≠ label w 0)
    (g : ℕ) (ng : w.length<2*g)
    (noShort : ∀ k, 4≤k → k<g → Even k → ¬HasCycle x y k) :
    HasCycle x y w.length := by
  let N := w.length
  have n0 : 0<N := by omega
  let : NeZero N := ⟨n0.ne'⟩
  let L (i : Fin N) : G := signPort x y i.val (label w i.val)
  have ds : 2∣N := by
    obtain ⟨b,eq⟩ := even
    exact ⟨b,by omega⟩
  have path_match (i : ℕ) (h : i≤N) : pathVal L i = path x y w i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pathVal,path,ih (by omega)]
      simp only [L,index_lt N (show i<N by omega)]
  have path0 : pathVal L N=1 := by
    have p := segment_product x y (path x y w) (label w) 0 0 w.length
      (by intro; intros; simp only [Nat.zero_add,path])
    have z : path x y w w.length=1 := by simpa [path,segment_label,closed] using p
    rw [path_match _ le_rfl]; exact z
  let a (i : ℕ) : Bool × G := (decide (i%2=1),pathVal L i)
  have sig (i : ℕ) : L (index N i)=signPort x y i (label w (i%N)) := by
    simp only [L,index,signPort,Nat.mod_mod_of_dvd _ ds]
  have step (i : ℕ) : (a (i+1)).2 = (a i).2 * signPort x y i (label w (i%N)) := by
    change pathVal L (i+1) = _
    rw [pathVal,sig]
  apply periodic_simple x y N g a n4 ng _ _ _ noShort
  · intro i
    apply Prod.ext
    · change decide ((i+N)%2=1)=decide (i%2=1)
      congr 1
      obtain ⟨q,e⟩ := even
      have h : (i+N)%2=i%2 := by change w.length=q+q at e; dsimp [N]; omega
      rw [h]
    · change pathVal L (i+N)=pathVal L i
      rw [Nat.add_comm i N,prefix_period,path0,one_mul]
  · intro i
    have f : (i+1)%2=1 ↔ i%2=0 := by omega
    have ports (c : Fin 3) : port x y c=1 ∨ port x y c=x ∨ port x y c=y := by
      fin_cases c <;> simp [port]
    have H := step i
    change pathVal L (i+1) = pathVal L i * signPort x y i (label w (i%N)) at H
    obtain z|z|z := ports (label w (i%N)) <;>
      (by_cases ev : i%2=0
       · have o := f.mpr ev
         simp [haarAdj,a,H,signPort,ev,o,z]
       · have o : i%2=1 := by omega
         have np : (i+1)%2≠1 := by omega
         simp [haarAdj,a,H,signPort,o,np,z,mul_assoc])
  · intro i h
    have H := congrArg Prod.snd h
    change (a (i+1+1)).2 = (a i).2 at H
    rw [step (i+1),step i,mul_assoc] at H
    have E := mul_left_cancel (H.trans (mul_one _).symm)
    have eql : port x y (label w (i%N))=port x y (label w ((i+1)%N)) := by
      by_cases ev : i%2=0
      · have ne : (i+1)%2≠0 := by omega
        simpa [signPort,ev,ne,mul_inv_eq_one] using E
      · have ne : (i+1)%2=0 := by omega
        simpa [signPort,ev,ne,inv_mul_eq_one] using E
    exact cyclic_labels w n4 good last i (port_inj x y hx hy hxy eql)

end HaarShortClosedIsCycle
#print axioms HaarShortClosedIsCycle.periodic_simple
#print axioms HaarShortClosedIsCycle.fromWord
