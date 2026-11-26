import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

namespace Ribbon

variable {G : Type*} [Group G]

def Adj (a b : G) (u v : Bool × G) : Prop :=
  (u.1 = false ∧ v.1 = false ∧ (u.2*a=v.2 ∨ v.2*a=u.2)) ∨
  (u.1 = true ∧ v.1 = true ∧ (u.2*b=v.2 ∨ v.2*b=u.2)) ∨
  (u.1 ≠ v.1 ∧ u.2 = v.2)

def Cycle (a b : G) (n : Nat) : Prop :=
  ∃ f : Fin n → Bool × G, Function.Injective f ∧
    ∀ i, Adj a b (f i) (f ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

def Normal (a b c : G) (i j k : ℤ) : G := b^j*a^i*c^k

def conjugate (x : G) : G →* G where
  toFun y := x*y*x⁻¹
  map_one' := by simp
  map_mul' := fun y z => by group

private theorem move_a (a b c : G) (r : a*b=b*a*c)
    (hc' : Commute c a) : conjugate a b = b*c := by
  change a*b*a⁻¹=b*c
  rw [r,mul_assoc, hc'.inv_right.eq]
  group

private theorem move_b (a b c : G) (hc : Commute c b) (r : a*b=b*a*c) :
    conjugate b a = a*c⁻¹ := by
  change b*a*b⁻¹=a*c⁻¹
  have h : b*a=a*b*c⁻¹ := by rw [r]; group
  rw [h,mul_assoc, (hc.inv_left.inv_right).eq]
  group

private theorem fixed_of_commute {a b : G} (h : Commute a b) :
    conjugate a b = b := by
  change a*b*a⁻¹=b
  rw [h.eq]; group

theorem conjugate_a_normal (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (i j k : ℤ) :
    conjugate a (Normal a b c i j k) = Normal a b c i j k * c^j := by
  simp only [Normal,map_mul,map_zpow, move_a a b c r ca,
    fixed_of_commute (Commute.refl a), fixed_of_commute ca.symm]
  rw [cb.symm.mul_zpow]
  have cc := ((Commute.refl c).zpow_zpow j k).eq
  rw [mul_assoc (b^j), (ca.zpow_zpow j i).eq]
  simp only [mul_assoc]
  rw [cc]

theorem conjugate_b_normal (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (i j k : ℤ) :
    conjugate b (Normal a b c i j k) = Normal a b c i j k * c^(-i) := by
  simp only [Normal,map_mul,map_zpow, move_b a b c cb r,
    fixed_of_commute (Commute.refl b), fixed_of_commute cb.symm]
  rw [ca.symm.inv_right.mul_zpow, inv_zpow, ←zpow_neg]
  have cc := ((Commute.refl c).zpow_zpow (-i) k).eq
  simp only [mul_assoc]
  rw [cc]

theorem signatures (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) {i j k i' j' k' : ℤ}
    (e : Normal a b c i j k = Normal a b c i' j' k') : c^i=c^i' ∧ c^j=c^j' := by
  have T := congrArg (conjugate a) e
  rw [conjugate_a_normal _ _ _ ca cb r,conjugate_a_normal _ _ _ ca cb r,e] at T
  have S := congrArg (conjugate b) e
  rw [conjugate_b_normal _ _ _ ca cb r,conjugate_b_normal _ _ _ ca cb r,e] at S
  have S' := congrArg (fun x : G => x⁻¹) (mul_left_cancel S)
  exact ⟨by simpa only [← zpow_neg, neg_neg] using S', mul_left_cancel T⟩


def asig : Fin 8 → ℤ := ![0,1,1,0,0,1,1,0]
def bsig : Fin 8 → ℤ := ![0,0,1,1,0,0,-1,-1]
def csig : Fin 8 → ℤ := ![0,0,1,1,1,1,0,0]
def vertex (a b c : G) (i : Fin 8) : G :=
  Normal a b c (asig i) (bsig i) (csig i)

theorem vertex_injective (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (hc : c≠1) (hc2 : c*c≠1) :
    Function.Injective (vertex a b c) := by
  have ci : c⁻¹≠1 := fun E => hc (by simpa using congrArg (fun x : G => x⁻¹) E)
  have cinv : c≠c⁻¹ := by
    intro h
    apply hc2
    calc c*c=c*c⁻¹ := congrArg (c*·) h
         _ = 1 := mul_inv_cancel c
  intro i j e
  obtain ⟨sa,sb⟩ := signatures a b c ca cb r e
  have sigInj : ∀ z z' : ℤ, (z=0 ∨ z=1 ∨ z= -1) → (z'=0 ∨ z'=1 ∨ z'= -1) →
      c^z=c^z' → z=z' := by
    rintro z z' (rfl|rfl|rfl) (rfl|rfl|rfl) h <;> simp_all
  have aeq : asig i = asig j := sigInj _ _
    (by fin_cases i <;> decide) (by fin_cases j <;> decide) sa
  have beq : bsig i = bsig j := sigInj _ _
    (by fin_cases i <;> decide) (by fin_cases j <;> decide) sb
  have ceq : csig i = csig j := by
    apply sigInj
    · fin_cases i <;> decide
    · fin_cases j <;> decide
    · change Normal a b c (asig i) (bsig i) (csig i) =
        Normal a b c (asig j) (bsig j) (csig j) at e
      rw [←aeq,←beq] at e
      exact mul_left_cancel e
  have H : ∀ u v : Fin 8, asig u = asig v → bsig u = bsig v → csig u = csig v → u = v :=
    by decide +kernel
  exact H i j aeq beq ceq

private theorem discard_a (a b c : G) (ca : Commute c a) {i j k j' k' : ℤ}
    (e : Normal a b c i j k=Normal a b c i j' k') : b^j*c^k=b^j'*c^k' := by
  unfold Normal at e
  rw [mul_assoc, (ca.zpow_zpow k i).symm.eq, ←mul_assoc,
    mul_assoc (b^j'), (ca.zpow_zpow k' i).symm.eq, ←mul_assoc] at e
  exact mul_right_cancel e

theorem vertex_injective' (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (hc : c≠1) (hbc : b*b*c≠1) :
    Function.Injective (vertex a b c) := by
  intro i j e
  obtain ⟨sa,sb⟩ := signatures a b c ca cb r e
  have sigInj : ∀ z z' : ℤ, (z=0 ∨ z=1) → (z'=0 ∨ z'=1) →
      c^z=c^z' → z=z' := by
    rintro z z' (rfl|rfl) (rfl|rfl) h <;> simp_all
  have aeq : asig i = asig j := sigInj _ _
    (by fin_cases i <;> decide) (by fin_cases j <;> decide) sa
  change Normal a b c (asig i) (bsig i) (csig i) =
        Normal a b c (asig j) (bsig j) (csig j) at e
  rw [←aeq] at e
  have t := discard_a a b c ca e
  have hb : b*c ≠ b⁻¹ := by
    intro he
    apply hbc
    calc b*b*c = b*(b*c) := mul_assoc _ _ _
        _ = 1 := by rw [he,mul_inv_cancel]
  have h0 : (1 : G) ≠ c := ne_comm.mp hc
  have h1 : (1 : G) ≠ c⁻¹ := by intro h; apply hc; simpa using (congrArg (fun x : G => x⁻¹) h).symm
  have ci : c⁻¹≠1 := Ne.symm h1
  fin_cases i <;> fin_cases j <;>
    (norm_num [asig] at aeq) <;> (norm_num [bsig,csig] at sb) <;>
    (norm_num [bsig,csig] at t) <;> first | rfl | contradiction | exact False.elim (hb (Eq.symm t))

def side : Fin 16 → Bool :=
  ![false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true]
def pos : Fin 16 → Fin 8 :=
  ![0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,0]

def walk (a b c : G) (i : Fin 16) : Bool × G := (side i, vertex a b c (pos i))

theorem walk_adj (a b c : G) (ca : Commute c a) (cb : Commute c b) (r : a*b=b*a*c) :
    ∀ i : Fin 16, Adj a b (walk a b c i)
      (walk a b c ⟨(i.val+1)%16,Nat.mod_lt _ (by decide)⟩) := by
  intro i
  fin_cases i <;> norm_num [Adj,walk,side,pos,vertex,Normal,asig,bsig,csig]
  · exact Or.inl r
  · exact Or.inr (by rw [mul_assoc,ca.eq,←mul_assoc])
  · exact Or.inr cb.eq
  · exact Or.inl ca.eq
  · exact Or.inr (by rw [mul_assoc, r]; group)

theorem walk_injective (a b c : G) (vInj : Function.Injective (vertex a b c)) :
    Function.Injective (walk a b c) := by
  have h : ∀ i j : Fin 16, side i=side j → pos i=pos j → i=j := by decide +kernel
  intro i j e
  exact h i j (congrArg Prod.fst e) (vInj (congrArg Prod.snd e))

/-- The two-rim ribbon of a class-two pair has a 16-cycle when the nontrivial
commutator is not an involution. No ambient finiteness condition is needed. -/
theorem cycle16 (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (hc : c≠1) (hc2 : c*c≠1) : Cycle a b 16 :=
  ⟨walk a b c,walk_injective a b c (vertex_injective a b c ca cb r hc hc2),walk_adj a b c ca cb r⟩

theorem rim_four (a b : G) (b2 : b*b≠1) (b4 : b^4=1) : Cycle a b 4 := by
  have d : orderOf b ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr b4
  have d' : ¬orderOf b ∣ 2 := fun d => b2 (by simpa [pow_two] using orderOf_dvd_iff_pow_eq_one.mp d)
  have hb : orderOf b ≤ 4 := Nat.le_of_dvd (by decide) d
  have E : orderOf b = 4 := by
    interval_cases h : orderOf b <;> simp_all
  let f : Fin 4 → Bool × G := fun j => (true, b^j.val)
  refine ⟨f,?_,?_⟩
  · intro i j eq
    have p : b^i.val=b^j.val := congrArg Prod.snd eq
    have h := pow_eq_pow_iff_modEq.mp p
    change i.val % orderOf b = j.val % orderOf b at h
    rw [E,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at h
    exact Fin.ext h
  · intro i
    refine Or.inr (Or.inl ⟨rfl,rfl,Or.inl ?_⟩)
    change b^i.val*b=b^((i.val+1)%4)
    rw [←pow_succ]
    by_cases H : i.val+1<4
    · rw [Nat.mod_eq_of_lt H]
    · have H' : i.val+1=4 := by omega
      rw [H',Nat.mod_self,pow_zero,b4]

theorem noncommuting (a b c : G) (ca : Commute c a) (cb : Commute c b)
    (r : a*b=b*a*c) (hc : c≠1) (hb : b*b≠1) :
    Cycle a b 4 ∨ Cycle a b 16 := by
  by_cases c2 : c*c=1
  · by_cases clash : b*b*c=1
    · left
      apply rim_four a b hb
      have t : b*b=c⁻¹ := by
        calc b*b=(b*b*c)*c⁻¹ := by group
          _ = c⁻¹ := by rw [clash,one_mul]
      have ci : c⁻¹*c⁻¹=1 := by simpa [mul_inv_rev] using congrArg (fun x : G => x⁻¹) c2
      calc b^4=(b*b)*(b*b) := by rw [show (4:Nat)=2+2 from rfl,pow_add,pow_two]
        _ = 1 := by rw [t,ci]
    · exact Or.inr ⟨walk a b c,walk_injective a b c (vertex_injective' a b c ca cb r hc clash),walk_adj a b c ca cb r⟩
  · exact Or.inr (cycle16 a b c ca cb r hc c2)

end Ribbon
#print axioms Ribbon.cycle16
#print axioms Ribbon.noncommuting
