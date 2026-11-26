import Mathlib.Tactic
import Mathlib.Algebra.Group.Commute.Basic

namespace HaarCycle

abbrev Coord := ℤ × ℤ × ℤ

def P : Fin 32 → Coord := fun i => (#[ (0,0,0), (0,0,0), (-1,0,0), (-1,1,-1),
  (-2,1,-1), (-2,1,-1), (-2,0,1), (-2,0,1),
  (-2,-1,3), (-1,-1,3), (-1,-1,3), (-1,0,2),
  (-2,0,2), (-2,0,2), (-2,-1,4), (-1,-1,4),
  (-1,-1,4), (-1,0,3), (-2,0,3), (-2,1,1),
  (-2,1,1), (-1,1,1), (-1,0,2), (0,0,2),
  (0,-1,2), (0,-1,2), (-1,-1,2), (-1,0,1),
  (-1,0,1), (-1,1,0), (-1,1,0), (0,1,0)] : Array Coord)[i.val]!

def side (i : Fin 32) : Bool := decide (i.val % 2 = 1)
def rightX (p : Coord) : Coord := (p.1+1,p.2.1,p.2.2)
def rightY (p : Coord) : Coord := (p.1,p.2.1+1,p.2.2+p.1)

theorem differentSide (i : Fin 32) : side i ≠ side (i+1) := by revert i; decide

def edge (p q : Coord) : Prop := q=p ∨ q=rightX p ∨ q=rightY p

instance (p q : Coord) : Decidable (edge p q) := by unfold edge; infer_instance

theorem walkCert (i : Fin 32) :
    if side i then edge (P (i+1)) (P i) else edge (P i) (P (i+1)) := by
  revert i
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem separationCert (i j : Fin 32) :
    i=j ∨ side i ≠ side j ∨
      (abs ((P i).1-(P j).1) ≤ 2 ∧ abs ((P i).2.1-(P j).2.1) ≤ 2 ∧
        ((P i).1=(P j).1 → (P i).2.1=(P j).2.1 →
          (P i).2.2-(P j).2.2=1 ∨ (P i).2.2-(P j).2.2=2 ∨
          (P j).2.2-(P i).2.2=1 ∨ (P j).2.2-(P i).2.2=2)) := by
  revert i j
  decide

variable {G : Type*} [Group G]

def norm (x y z : G) (p : Coord) := y^p.2.1 * x^p.1 * z^p.2.2

theorem normX (x y z : G) (h : Commute z x) (p : Coord) :
    norm x y z (rightX p) = norm x y z p*x := by
  unfold norm rightX
  simp only [zpow_add_one]
  simp only [mul_assoc]
  rw [← (h.zpow_left p.2.2).eq]

theorem normY (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (p : Coord) :
    norm x y z (rightY p) = norm x y z p*y := by
  have hS : SemiconjBy y (x*z) x := by
    change y*(x*z)=x*y
    rw [← mul_assoc,h]
  have hC := (hS.zpow_right p.1)
  change y*((x*z)^p.1) = x^p.1*y at hC
  rw [cx.symm.mul_zpow] at hC
  calc
    norm x y z (rightY p) = y^p.2.1 * (y * (x^p.1*z^p.1)) * z^p.2.2 := by
      simp only [norm,rightY,zpow_add,zpow_one]
      have e : z^p.2.2*z^p.1=z^p.1*z^p.2.2 := (Commute.refl z).zpow_zpow _ _ |>.eq
      rw [e]
      simp only [mul_assoc]
    _ = norm x y z p*y := by
      rw [hC]
      have e := (cy.zpow_left p.2.2).eq
      simp only [norm,mul_assoc]
      rw [e]

def haarAdj (x y : G) (p q : Bool × G) : Prop :=
  if p.1 then q.1 = false ∧ (p.2=q.2 ∨ p.2=q.2*x ∨ p.2=q.2*y)
  else q.1 = true ∧ (q.2=p.2 ∨ q.2=p.2*x ∨ q.2=p.2*y)

def vert (x y z : G) (i : Fin 32) : Bool × G := (side i,norm x y z (P i))

theorem hasAdj (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (i : Fin 32) :
    haarAdj x y (vert x y z i) (vert x y z (i+1)) := by
  have transfer (p q : Coord) (e : edge p q) :
      norm x y z q = norm x y z p ∨ norm x y z q = norm x y z p*x ∨
        norm x y z q = norm x y z p*y := by
    rcases e with e | e | e
    · exact Or.inl (congrArg _ e)
    · exact Or.inr (Or.inl ((congrArg _ e).trans (normX x y z cx p)))
    · exact Or.inr (Or.inr ((congrArg _ e).trans (normY x y z cx cy h p)))
  have hCert := walkCert i
  have hs := differentSide i
  cases h1 : side i <;> cases h2 : side (i+1) <;>
    simp [h1,h2] at hs hCert
  · exact (by simpa [haarAdj,vert,h1,h2] using transfer _ _ hCert)
  · exact (by simpa [haarAdj,vert,h1,h2] using transfer _ _ hCert)

theorem centralNE (z : G) (h1 : z ≠ 1) (h2 : z^2 ≠ 1) (i j : ℤ)
    (h : i-j=1 ∨ i-j=2 ∨ j-i=1 ∨ j-i=2) : z^i ≠ z^j := by
  intro hg
  have e (u v : ℤ) (hu : z^u=z^v) : z^(u-v)=1 := by rw [zpow_sub,hu,mul_inv_cancel]
  rcases h with q | q | q | q
  · exact h1 (by simpa [q] using e i j hg)
  · exact h2 (by simpa [q] using e i j hg)
  · exact h1 (by simpa [q] using e j i hg.symm)
  · exact h2 (by simpa [q] using e j i hg.symm)

theorem simple (x y z : G) (h1 : z ≠ 1) (h2 : z^2 ≠ 1)
    (sep : ∀ p q : Coord, |p.1-q.1|≤2 → |p.2.1-q.2.1|≤2 →
       norm x y z p=norm x y z q → p.1=q.1 ∧ p.2.1=q.2.1) :
    Function.Injective (vert x y z) := by
  intro i j h
  rcases separationCert i j with e | e | ⟨d1,d2,t⟩
  · exact e
  · exact False.elim (e (congrArg Prod.fst h))
  · have heq := congrArg Prod.snd h
    obtain ⟨e1,e2⟩ := sep _ _ d1 d2 heq
    exact False.elim ((centralNE z h1 h2 _ _ (t e1 e2)) (by
      change norm x y z (P i) = norm x y z (P j) at heq
      unfold norm at heq
      rw [e1,e2] at heq
      exact mul_left_cancel heq))

theorem certified_cycle (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z ≠ 1) (h2 : z^2 ≠ 1)
    (sep : ∀ p q : Coord, |p.1-q.1|≤2 → |p.2.1-q.2.1|≤2 →
       norm x y z p=norm x y z q → p.1=q.1 ∧ p.2.1=q.2.1) :
    ∃ v : Fin 32 → Bool × G, Function.Injective v ∧
      ∀ i, haarAdj x y (v i) (v (i+1)) :=
  ⟨vert x y z,simple x y z h1 h2 sep,hasAdj x y z cx cy rel⟩

end HaarCycle
#print axioms HaarCycle.certified_cycle

namespace HaarCycle

variable {G : Type*} [Group G]

theorem shift (x y z : G) (cx : Commute z x)
    (h : x*y=y*x*z) (i : ℤ) :
    x^i*y=y*x^i*z^i := by
  have hs : SemiconjBy y (x*z) x := by
    change y*(x*z)=x*y
    rw [← mul_assoc,h]
  have hc := hs.zpow_right i
  change y*(x*z)^i=x^i*y at hc
  rw [cx.symm.mul_zpow, ← mul_assoc] at hc
  exact hc.symm

theorem normShiftY (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (p : Coord) :
    norm x y z p*y=y*norm x y z p*z^p.1 := by
  have e := (cy.zpow_left p.2.2).eq
  have ez := ((Commute.refl z).zpow_zpow p.1 p.2.2).eq
  have ey := ((Commute.refl y).zpow_left p.2.1).eq
  calc
    norm x y z p*y = y^p.2.1 * (x^p.1*y) * z^p.2.2 := by
      simp only [norm,mul_assoc]; rw [e]
    _ = (y^p.2.1*y)*x^p.1*(z^p.1*z^p.2.2) := by rw [shift x y z cx h]; simp only [mul_assoc]
    _ = y*norm x y z p*z^p.1 := by rw [ey,ez]; simp only [norm,mul_assoc]

theorem normShiftX (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (p : Coord) :
    norm x y z p*x=x*norm x y z p*z^(-p.2.1) := by
  have hr : y*x=x*y*z⁻¹ := by rw [h,mul_assoc (y*x),mul_inv_cancel,mul_one]
  have hp := shift y x z⁻¹ cy.inv_left hr p.2.1
  rw [inv_zpow] at hp
  have ex := (cx.zpow_left p.2.2).eq
  have exi := ((Commute.refl x).zpow_left p.1).eq
  have ez := ((cx.zpow_zpow (-p.2.1) p.1).eq)
  have ezz := ((Commute.refl z).zpow_zpow (-p.2.1) p.2.2).eq
  calc
    norm x y z p*x = (y^p.2.1*x)*x^p.1*z^p.2.2 := by
      simp only [norm,mul_assoc]; rw [ex, ← mul_assoc (x^p.1) x _, exi, mul_assoc]
    _ = (x*y^p.2.1)*(z^(-p.2.1)*x^p.1)*z^p.2.2 := by rw [hp]; simp only [mul_assoc,zpow_neg]
    _ = x*norm x y z p*z^(-p.2.1) := by rw [ez]; simp only [norm,mul_assoc]; rw [ezz]

theorem from_bounded_eq (z : G) (h1 : z≠1) (h2 : z^2≠1)
    {m n : ℤ} (hb : |m-n|≤2) (eq : z^m=z^n) : m=n := by
  by_contra hn
  have h := abs_le.mp hb
  apply centralNE z h1 h2 m n _ eq
  omega

theorem autoSep (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) (h2 : z^2≠1)
    (p q : Coord) (b1 : |p.1-q.1|≤2) (b2 : |p.2.1-q.2.1|≤2)
    (e : norm x y z p=norm x y z q) :
    p.1=q.1 ∧ p.2.1=q.2.1 := by
  constructor
  · apply from_bounded_eq z h1 h2 b1
    apply mul_left_cancel (a := y*norm x y z p)
    rw [← normShiftY x y z cx cy rel p,e,normShiftY x y z cx cy rel q,←e]
  · have hb : |-p.2.1 - -q.2.1|≤2 := by
      have h : -p.2.1 - -q.2.1 = -(p.2.1-q.2.1) := by ring
      rw [h,abs_neg]
      exact b2
    have hg : z^(-p.2.1)=z^(-q.2.1) := by
      apply mul_left_cancel (a := x*norm x y z p)
      rw [← normShiftX x y z cx cy rel p,e,normShiftX x y z cx cy rel q,←e]
    have := from_bounded_eq z h1 h2 hb hg
    omega

theorem commutator_cycle (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) (h2 : z^2≠1) :
    ∃ v : Fin 32 → Bool × G, Function.Injective v ∧
      ∀ i, haarAdj x y (v i) (v (i+1)) :=
  certified_cycle x y z cx cy rel h1 h2 (autoSep x y z cx cy rel h1 h2)

end HaarCycle

#print axioms HaarCycle.commutator_cycle
