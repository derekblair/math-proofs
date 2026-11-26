import HomologyThree

namespace HomologyThree

open HaarDerivedCoverTransfer HaarDerivedFlowPositive
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

private def accum (p : Nat → V) : Nat → Lamp V
  | 0 => 0
  | k+1 => accum p k + bump (p k) (p (k+1))

private theorem shift_accum {p : Nat → V} {n : Nat}
    (per : ∀ i, p (i+n) = p i) (i : Nat) :
    accum p (i+n) = accum p i + accum p n := by
  induction i with
  | zero => simp [accum]
  | succ i ih =>
      rw [show i+1+n=(i+n)+1 by omega, accum, ih, per, show i+n+1=(i+1)+n by omega,
        per, accum]
      abel

private theorem first_dart {n : Nat} (hn : 3 ≤ n) (v : Fin n → V)
    (inj : Function.Injective v) :
    accum (periodicLift n (by omega) v) n
      (periodicLift n (by omega) v 0, periodicLift n (by omega) v 1) = 1 := by
  let p := periodicLift n (by omega) v
  let q := (p 0,p 1)
  change accum p n q = _
  have same (i j : Nat) (h : p i = p j) : i%n=j%n :=
    congrArg Fin.val (inj h)
  have step (k : Nat) (h : k<n) :
      bump (p k) (p (k+1)) q = if k=0 then 1 else 0 := by
    have noBack : (p (k+1),p k) ≠ q := by
      intro eq
      have a := same (k+1) 0 (congrArg Prod.fst eq)
      have b := same k 1 (congrArg Prod.snd eq)
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega : 1<n)] at b
      subst k
      simp [Nat.mod_eq_of_lt (by omega : 2<n)] at a
    have fw : (p k,p (k+1)) = q ↔ k = 0 := by
      constructor
      · intro eq
        have a := same k 0 (congrArg Prod.fst eq)
        rwa [Nat.mod_eq_of_lt h, Nat.zero_mod] at a
      · rintro rfl
        rfl
    simp [bump, noBack, fw]
  have calcAccum (k : Nat) (hk : k ≤ n) :
      accum p k q = if k=0 then 0 else 1 := by
    induction k with
    | zero => simp [accum]
    | succ k ih =>
      have h : k < n := by omega
      simp only [accum, Pi.add_apply]
      rw [ih (by omega), step k h]
      by_cases E : k=0 <;> simp [E]
  simpa [show n≠0 by omega] using calcAccum n (by omega)

/-- Every simple cycle of length at least three lifts to a simple cycle
of triple its length in the full all-edge mod-three lift. -/
theorem triple_upper (R : V → V → Prop) (n : Nat) (hn : 3≤n)
    (base : Cyclic R n) : Cyclic (liftEdge R) (3*n) := by
  obtain ⟨v,vi,ve⟩ := base
  let p := periodicLift n (by omega) v
  let L := accum p
  let D := L n
  let q := (p 0,p 1)
  have Dq : D q = 1 := first_dart hn v vi
  have per : ∀ i, p (i+n) = p i := periodic n (by omega) v
  have lper (i : Nat) : L (i+n) = L i + D := shift_accum per i
  have P (i k : Nat) : p (i+n*k) = p i := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, ←Nat.add_assoc, per,ih]
  have S (i k : Nat) : L (i+n*k) = L i + k • D := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, ←Nat.add_assoc,lper,ih,succ_nsmul,add_assoc]
  have pc : p (3*n) = p 0 := by simpa [Nat.mul_comm] using P 0 3
  have lc : L (3*n) = L 0 := by
    have hD : (3 : Nat) • D = 0 := by
      ext z
      change (3 : Nat) • (D z) = (0 : ZMod 3)
      rw [nsmul_eq_mul]
      have H : ((3 : Nat) : ZMod 3) = 0 := by decide
      rw [H, zero_mul]
    simpa [Nat.mul_comm, hD] using S 0 3
  let f : Fin (3*n) → V × Lamp V := fun j => (p j.val,L j.val)
  refine ⟨f,?_,?_⟩
  · intro a b eq
    have hmod : a.val%n = b.val%n :=
      congrArg Fin.val (vi (congrArg Prod.fst eq))
    have La : L a.val = L b.val := congrArg Prod.snd eq
    have decomp (i : Nat) : L i = L (i%n) + (i/n) • D :=
      (congrArg L (Nat.mod_add_div i n)).symm.trans (S _ _)
    rw [decomp a.val, decomp b.val, hmod, add_right_inj] at La
    have e : (((a.val/n : Nat) : ZMod 3)) = (((b.val/n : Nat) : ZMod 3)) := by
      have eqn := congrArg (fun f : Lamp V => f q) La
      change (a.val/n) • (D q) = (b.val/n) • (D q) at eqn
      simpa [Dq, nsmul_eq_mul] using eqn
    have ha : a.val/n<3 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Nat.mul_comm] using a.isLt)
    have hb : b.val/n<3 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Nat.mul_comm] using b.isLt)
    have ediv : a.val/n = b.val/n := by
      have e' := congrArg ZMod.val e
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e'
      exact e'
    apply Fin.ext
    rw [←Nat.mod_add_div a.val n, ←Nat.mod_add_div b.val n, hmod,ediv]
  · intro i
    have E : liftEdge R (p i.val,L i.val) (p (i.val+1), L (i.val+1)) :=
      ⟨nat_edge (by omega) R v ve _, rfl⟩
    change liftEdge R (p i.val,L i.val) (p ((i.val+1)%(3*n)),L ((i.val+1)%(3*n)))
    by_cases h : i.val+1<3*n
    · simpa [Nat.mod_eq_of_lt h] using E
    · have he : i.val+1=3*n := by omega
      rw [he, Nat.mod_self]
      rwa [he, pc, lc] at E

end HomologyThree
#print axioms HomologyThree.triple_upper
