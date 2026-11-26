import HaarDerivedHaarTransfer
namespace HomologyThree
open HaarDerivedCoverTransfer HaarDerivedModThree HaarDerivedFlowPositive
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

abbrev Lamp (V : Type*) := (V × V) → ZMod 3
def bump (u v : V) (q : V × V) : ZMod 3 :=
  (if (u,v)=q then 1 else 0)-(if (v,u)=q then 1 else 0)
def liftEdge (R : V→V→Prop) (a b : V × Lamp V) : Prop :=
  R a.1 b.1 ∧ a.2+bump a.1 b.1=b.2

theorem liftSymm (R : V→V→Prop) (symm : ∀ {u v}, R u v → R v u)
    {a b : V × Lamp V} (e : liftEdge R a b) : liftEdge R b a := by
  refine ⟨symm e.1,?_⟩
  rw [←e.2]
  funext z
  simp only [Pi.add_apply,bump]
  abel

theorem localInj (R : V→V→Prop) {a b c : V × Lamp V}
    (e : liftEdge R a b) (f : liftEdge R a c) (h : b.1=c.1) : b=c := by
  apply Prod.ext h
  rw [←e.2,←f.2,h]

variable [Fintype V]

theorem lamp_div (a : Nat→V) (n : ℕ) (q r : V) (L : Nat→ZMod 3)
    (eq : L n=L 0)
    (upd : ∀ i<n, L (i+1)=L i+bump (a i) (a (i+1)) (q,r)) :
    (3:ℤ) ∣ flow a n q r := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  calc
    (flow a n q r : ZMod 3) = ∑ i : Fin n, bump (a i.val) (a (i.val+1)) (q,r) := by
      unfold flow count
      rw [Int.cast_sub,Int.cast_sum,Int.cast_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have comm : (a (i.val+1)=q ∧ a i.val=r) ↔ (a i.val=r ∧ a (i.val+1)=q) := and_comm
      simp only [bump,Prod.mk.injEq,comm,Int.cast_ite,Int.cast_zero,Int.cast_one]
    _ = ∑ i : Fin n, (L (i.val+1)-L i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [upd i.val i.isLt]
      abel
    _ = 0 := by rw [HaarDerivedHaarTransfer.telescope,eq,sub_self]

theorem triple_lower (R : V→V→Prop) (symm : ∀ {u v}, R u v → R v u)
    (loop : ∀ u, ¬R u u) (h : ℕ)
    (base : ∀ k, 3≤k → Cyclic R k → 2*h≤k)
    (n : ℕ) (hn : 3≤n) (C : Cyclic (liftEdge R) n) : 3*(2*h)≤n := by
  obtain ⟨v,vi,ve⟩ := C
  apply bound_of_cycle hn h Prod.fst (liftEdge R) R
    (liftSymm R symm) symm loop (fun e => e.1) (localInj R) base v vi ve
  intro q r
  let p := periodicLift n (by omega : 0<n) v
  refine lamp_div (fun i => (p i).1) n q r (fun i => (p i).2 (q,r)) ?_ ?_
  · have eq := periodic n (by omega : 0<n) v 0
    simpa only [Nat.zero_add] using congrArg (fun t : V × Lamp V => t.2 (q,r)) eq
  · intro i hi
    have e := nat_edge (by omega : 0<n) (liftEdge R) v ve i
    exact congrArg (fun w : Lamp V => w (q,r)) e.2 |>.symm

end HomologyThree
#print axioms HomologyThree.triple_lower
