import HaarDerivedCoverTransfer
import HaarReducedWalkCycle
import HaarShortClosedIsCycle
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

namespace HaarDerivedHaarTransfer
open HaarDerivedFlowPositive HaarDerivedModThree HaarDerivedZeroFlow HaarDerivedCoverTransfer
open HaarAllNoncommuting HaarCycle
open HaarHalfCollision (port branch symmetric)

variable {G H : Type*} [Group G] [Group H]

def project (f : G →* H) (u : Bool × G) : Bool × H := (u.1,f u.2)

theorem no_loop (x y : G) (u : Bool × G) : ¬haarAdj x y u u := by
  cases e : u.1 <;> simp [haarAdj,e]

theorem adj_map (f : G →* H) (x y : G) {u v : Bool × G} (h : haarAdj x y u v) :
    haarAdj (f x) (f y) (project f u) (project f v) := by
  cases z : u.1 <;> simp only [haarAdj,z,ite_true,ite_false,project] at h ⊢
  all_goals
    obtain ⟨hv,s|s|s⟩ := h
    · exact ⟨hv, Or.inl (congrArg f s)⟩
    · exact ⟨hv, Or.inr (Or.inl (by simpa only [map_mul] using congrArg f s))⟩
    · exact ⟨hv, Or.inr (Or.inr (by simpa only [map_mul] using congrArg f s))⟩

theorem map_port (f : G →* H) (x y : G) (j : Fin 3) :
    f (port x y j)=port (f x) (f y) j := by
  fin_cases j <;> simp [port]

theorem locally_inj (f : G →* H) (x y : G)
    (hx : f x≠1) (hy : f y≠1) (hxy : f x≠f y)
    {u v w : Bool × G} (e : haarAdj x y u v) (d : haarAdj x y u w)
    (eq : project f v=project f w) : v=w := by
  obtain ⟨vside,j,hj⟩ := branch x y u v e
  obtain ⟨wside,k,hk⟩ := branch x y u w d
  have E : f v.2=f w.2 := congrArg (fun q : Bool × H => q.2) eq
  have porteq : port (f x) (f y) j=port (f x) (f y) k := by
    cases s : u.1
    · simp only [hj,hk,s,Bool.false_eq_true,ite_false,map_mul,map_port] at E
      exact mul_left_cancel E
    · simp only [hj,hk,s,ite_true,map_mul,map_inv,map_port] at E
      exact inv_injective (mul_left_cancel E)
  have jk := HaarReducedWalkCycle.port_inj (f x) (f y) hx hy hxy porteq
  subst k
  exact Prod.ext (vside.trans wside.symm) (hj.trans hk.symm)

def trace {n : Nat} (f : G →* H) (hn : 0<n) (v : Fin n → Bool × G) (i : Nat) : Bool × H :=
  project f (periodicLift n hn v i)

theorem even_cycle (x y : G) {n : Nat} (hn : 0<n) (cy : HasCycle x y n) : Even n := by
  obtain ⟨v,_,e⟩ := cy
  let a := periodicLift n hn v
  have edges (i : Nat) : haarAdj x y (a i) (a (i+1)) := nat_edge hn (haarAdj x y) v e i
  have flip (i : Nat) : (a (i+1)).1 = !(a i).1 := (branch x y _ _ (edges i)).1
  have closed : a (0+n)=a 0 := periodic n hn v 0
  have p := HaarShortClosedIsCycle.parity_return a flip 0 n closed
  exact ⟨n/2,by omega⟩

section FiniteBase
variable [Fintype H] [DecidableEq H]

theorem missing_div {a : Nat → Bool × H} {N : Nat} (N0 : 1<N)
    (period : ∀ i, a (i+N)=a i) (skip : (Bool × H) → Bool × H)
    (d : ∀ u v, v≠skip u → (3:ℤ) ∣ flow a N u v) :
    ∀ u v, (3:ℤ) ∣ flow a N u v := by
  intro u v
  by_cases K : v=skip u
  · subst v
    let E : Finset (Bool × H) := Finset.univ.erase (skip u)
    have Z : (3:ℤ) ∣ ∑ w ∈ E, flow a N u w :=
      Finset.dvd_sum (fun w hw => d u w (Finset.mem_erase.mp hw).1)
    have Y := Finset.sum_erase_add (s:=Finset.univ) (f:=flow a N u) (Finset.mem_univ (skip u))
    rw [flow_balance a N N0 period u] at Y
    have L : flow a N u (skip u) = - ∑ w ∈ E, flow a N u w := by
      unfold E
      omega
    rw [L]
    exact dvd_neg.mpr Z
  · exact d u v K

theorem nonedge_zero (X Y : H) (a : Nat → Bool × H) (N : Nat)
    (step : ∀ i, haarAdj X Y (a i) (a (i+1))) (u v : Bool × H) (Hn : ¬haarAdj X Y u v) :
    flow a N u v=0 := by
  have absent {p q : Bool × H} (bad : ¬haarAdj X Y p q) : count a N p q=0 := by
    have NN := count_nonneg a N p q
    by_contra nz
    have pos : 0<count a N p q := by omega
    obtain ⟨i,ep,eq⟩ := (count_pos a N p q).mp pos
    exact bad (by simpa only [ep,eq] using step i.val)
  simp only [flow,absent Hn,absent (fun H => Hn (symmetric X Y H)),sub_zero]

theorem bound_of_haar_cycle (f : G →* H) (x y : G)
    (hx : f x≠1) (hy : f y≠1) (hxy : f x≠f y)
    {n : Nat} (hn : 3≤n) (h : Nat)
    (baseGirth : ∀ k, 3≤k → HasCycle (f x) (f y) k → 2*h≤k)
    (v : Fin n → Bool × G) (inj : Function.Injective v)
    (adj : ∀ i, haarAdj x y (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (by omega)⟩))
    (nonmatching : ∀ u w, haarAdj (f x) (f y) u w → u.2≠w.2 →
      (3:ℤ) ∣ flow (trace f (by omega) v) n u w) :
    3*(2*h)≤n := by
  let a := trace f (by omega) v
  have per : ∀ i, a (i+n)=a i := fun i => congrArg (project f) (periodic n (by omega) v i)
  have E : ∀ i, haarAdj (f x) (f y) (a i) (a (i+1)) :=
    fun i => adj_map f x y (nat_edge (by omega) (haarAdj x y) v adj i)
  have all : ∀ u w, (3:ℤ) ∣ flow a n u w := by
    apply missing_div (by omega : 1<n) per (fun u => (!u.1,u.2))
    intro u w hp
    by_cases edge : haarAdj (f x) (f y) u w
    · have hs := (branch (f x) (f y) u w edge).1
      have hh : u.2≠w.2 := fun eq => hp (Prod.ext hs eq.symm)
      exact nonmatching u w edge hh
    · rw [nonedge_zero (f x) (f y) a n E u w edge]
      exact dvd_zero _
  exact bound_of_cycle hn h (project f) (haarAdj x y) (haarAdj (f x) (f y))
    (symmetric x y) (symmetric (f x) (f y)) (no_loop (f x) (f y)) (adj_map f x y)
    (locally_inj f x y hx hy hxy) baseGirth v inj adj all

theorem cast_flow (a : Nat → Bool × H) (N : Nat) (u v : Bool × H) :
    (flow a N u v : ZMod 3) =
      ∑ i : Fin N, ((if a i.val=u ∧ a (i.val+1)=v then 1 else 0) -
        (if a i.val=v ∧ a (i.val+1)=u then 1 else 0)) := by
  unfold flow count
  rw [Int.cast_sub,Int.cast_sum,Int.cast_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases x : a i.val=u ∧ a (i.val+1)=v <;>
    by_cases y : a i.val=v ∧ a (i.val+1)=u <;> simp [x,y]

theorem div_of_lamp_zero (a : Nat → Bool × H) (N : Nat) (u v : Bool × H)
    (hz : (∑ i : Fin N, ((if a i.val=u ∧ a (i.val+1)=v then (1:ZMod 3) else 0) -
        (if a i.val=v ∧ a (i.val+1)=u then 1 else 0)))=0) :
    (3:ℤ) ∣ flow a N u v := by
  rw [←cast_flow] at hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

theorem telescope {A : Type*} [AddCommGroup A] (f : Nat → A) (n : Nat) :
    (∑ i : Fin n, (f (i.val+1)-f i.val)) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    abel

theorem div_of_lamp_update (a : Nat → Bool × H) (N : Nat) (u v : Bool × H)
    (lamp : Nat → ZMod 3) (cl : lamp N=lamp 0)
    (update : ∀ i<N, lamp (i+1)=lamp i +
      ((if a i=u ∧ a (i+1)=v then (1:ZMod 3) else 0) -
        (if a i=v ∧ a (i+1)=u then 1 else 0))) :
    (3:ℤ) ∣ flow a N u v := by
  apply div_of_lamp_zero
  calc
    _ = ∑ i : Fin N, (lamp (i.val+1)-lamp i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [update i.val i.isLt]
      abel
    _ = 0 := by rw [telescope,cl,sub_self]

end FiniteBase
end HaarDerivedHaarTransfer
#print axioms HaarDerivedHaarTransfer.bound_of_haar_cycle
#print axioms HaarDerivedHaarTransfer.div_of_lamp_zero
#print axioms HaarDerivedHaarTransfer.div_of_lamp_update
#print axioms HaarDerivedHaarTransfer.even_cycle
