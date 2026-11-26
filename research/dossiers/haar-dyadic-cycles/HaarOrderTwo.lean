import HaarCycle

namespace HaarOrderTwo

open HaarCycle
variable {G : Type*} [Group G]

def P16 : Fin 16 → Coord := fun i => (#[ (0,0,0), (0,0,0), (-1,0,0), (-1,1,-1),
  (-2,1,-1), (-2,2,-3), (-2,2,-3), (-1,2,-3),
  (-1,1,-2), (-1,1,-2), (-1,0,-1), (0,0,-1),
  (0,-1,-1), (1,-1,-1), (1,-1,-1), (1,0,0)] : Array Coord)[i.val]!

def side16 (i : Fin 16) : Bool := decide (i.val % 2 = 1)
def v16 (x y z : G) (i : Fin 16) : Bool × G := (side16 i,HaarCycle.norm x y z (P16 i))

theorem cert16 (i : Fin 16) :
    (side16 i ≠ side16 (i+1)) ∧
    (if side16 i then edge (P16 (i+1)) (P16 i) else edge (P16 i) (P16 (i+1))) := by
  revert i
  decide

theorem adj16 (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (i : Fin 16) :
    haarAdj x y (v16 x y z i) (v16 x y z (i+1)) := by
  have transfer (p q : Coord) (e : edge p q) :
      HaarCycle.norm x y z q = HaarCycle.norm x y z p ∨ HaarCycle.norm x y z q = HaarCycle.norm x y z p*x ∨
        HaarCycle.norm x y z q = HaarCycle.norm x y z p*y := by
    rcases e with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (normX x y z cx p))
    · exact Or.inr (Or.inr (normY x y z cx cy h p))
  obtain ⟨hs,hCert⟩ := cert16 i
  cases h1 : side16 i <;> cases h2 : side16 (i+1) <;>
    simp [h1,h2] at hs hCert
  · exact (by simpa [haarAdj,v16,h1,h2] using transfer _ _ hCert)
  · exact (by simpa [haarAdj,v16,h1,h2] using transfer _ _ hCert)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem sep16 (i j : Fin 16) :
    i=j ∨ side16 i ≠ side16 j ∨
    let p := P16 i; let q := P16 j
    (p.1-q.1)%2≠0 ∨ (p.2.1-q.2.1)%2≠0 ∨
    ((p.1=q.1 ∧ p.2.1=q.2.1 ∧
      (p.2.2-q.2.2=1 ∨ q.2.2-p.2.2=1)) ∨
    (q.1-p.1= -2 ∧ q.2.1-p.2.1=2) ∨ (p.1-q.1= -2 ∧ p.2.1-q.2.1=2)) := by
  revert i j
  decide

theorem power_even (z : G) (h1 : z≠1) (h2 : z^2=1) {m n : ℤ}
    (he : z^m=z^n) : (m-n)%2=0 := by
  have hh : z^(m-n)=1 := by rw [zpow_sub,he,mul_inv_cancel]
  by_contra hn
  have heq : m-n = 2*((m-n)/2)+1 := by omega
  rw [heq,zpow_add_one,zpow_mul] at hh
  have ht : z^(2:ℤ)=1 := by exact_mod_cast h2
  rw [ht,one_zpow,one_mul] at hh
  exact h1 hh

theorem commute_powers (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (i j : ℤ) :
    x^i*y^j = y^j*x^i*z^(i*j) := by
  have c := (cx.zpow_zpow i i).eq
  have hS : SemiconjBy (x^i) y (y*z^i) := by
    change x^i*y=(y*z^i)*x^i
    rw [shift x y z cx h, mul_assoc,mul_assoc,c]
  have hP := hS.zpow_right j
  change x^i*y^j=(y*z^i)^j*x^i at hP
  rw [((cy.zpow_left i).symm.mul_zpow), ← zpow_mul] at hP
  calc
    x^i*y^j = y^j*z^(i*j)*x^i := hP
    _ = _ := by rw [mul_assoc,(cx.zpow_zpow (i*j) i).eq,← mul_assoc]

def prod (p q : Coord) : Coord :=
  (p.1+q.1,p.2.1+q.2.1,p.2.2+q.2.2+p.1*q.2.1)

theorem norm_prod (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (h : x*y=y*x*z) (p q : Coord) :
    HaarCycle.norm x y z (prod p q)=HaarCycle.norm x y z p * HaarCycle.norm x y z q := by
  have e1 := (cx.zpow_zpow (p.1*q.2.1) q.1).eq
  have e2 := (cx.zpow_zpow p.2.2 q.1).eq
  have e3 := (cy.zpow_zpow p.2.2 q.2.1).eq
  rw [HaarCycle.norm,HaarCycle.norm,HaarCycle.norm,prod]
  simp only [zpow_add]
  have e4 := ((Commute.refl z).zpow_zpow q.2.2 (p.1*q.2.1)).eq
  have e5 := ((Commute.refl z).zpow_zpow p.2.2 (p.1*q.2.1)).eq
  have swap {a b : G} (e : a*b=b*a) (c : G) : a*(b*c)=b*(a*c) := by
    rw [←mul_assoc,e,mul_assoc]
  calc
    (y^p.2.1*y^q.2.1)*(x^p.1*x^q.1)*(z^p.2.2*z^q.2.2*z^(p.1*q.2.1)) =
        y^p.2.1 * ((y^q.2.1*x^p.1*z^(p.1*q.2.1))*z^p.2.2*x^q.1) * z^q.2.2 := by
      simp only [mul_assoc]
      rw [swap e2,swap e1,swap e5.symm,e4]
    _ = _ := by
      rw [← commute_powers x y z cx cy h]
      simp only [mul_assoc]
      rw [swap e3]

theorem offset_fourth (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h2 : z^2=1) (p q : Coord)
    (e1 : q.1-p.1= -2) (e2 : q.2.1-p.2.1=2)
    (h : HaarCycle.norm x y z p=HaarCycle.norm x y z q) : (x⁻¹*y)^4=1 := by
  let d : Coord := (q.1-p.1,q.2.1-p.2.1,q.2.2-p.2.2-p.1*(q.2.1-p.2.1))
  have ee : prod p d=q := by
    apply Prod.ext
    · simp [prod,d]
    · apply Prod.ext
      · simp [prod,d]
      · simp [prod,d]; ring
  have check := norm_prod x y z cx cy rel p d
  rw [ee,← h] at check
  have hn : HaarCycle.norm x y z d=1 := mul_left_cancel (((mul_one _).trans check).symm)
  have hv : HaarCycle.norm x y z ((-1,1,-1) : Coord)=x⁻¹*y := by
    have j := (commute_powers x y z cx cy rel (-1) 1)
    simpa [HaarCycle.norm,mul_assoc] using j.symm
  have hh : (x⁻¹*y)^2=HaarCycle.norm x y z (-2,2,-3) := by
    rw [pow_two,←hv,←norm_prod x y z cx cy rel]
    rfl
  have d1 : d.1= -2 := e1
  have d2 : d.2.1=2 := e2
  have e : HaarCycle.norm x y z (-2,2,-3) = HaarCycle.norm x y z d * z^((-3:ℤ)-d.2.2) := by
    simp only [HaarCycle.norm,d1,d2]
    simp only [mul_assoc,←zpow_add]
    have h : d.2.2+(-3-d.2.2)=(-3:ℤ) := by omega
    rw [h]
  rw [show 4=2*2 by decide,pow_mul,hh,e,hn,one_mul]
  have ht : z^(2:ℤ)=1 := by exact_mod_cast h2
  rw [← zpow_natCast,←zpow_mul,mul_comm,zpow_mul]; norm_cast; rw [h2,one_zpow]

theorem choose (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) (h2 : z^2=1) :
    Function.Injective (v16 x y z) ∨ (x⁻¹*y)^4=1 := by
  by_cases hv : (x⁻¹*y)^4=1
  · exact Or.inr hv
  · left
    intro i j e
    have hn := congrArg Prod.snd e
    change HaarCycle.norm x y z (P16 i)=HaarCycle.norm x y z (P16 j) at hn
    rcases sep16 i j with eq | side | X | Y | H | H | H
    · exact eq
    · exact False.elim (side (congrArg Prod.fst e))
    · exfalso
      apply X
      apply power_even z h1 h2
      apply mul_left_cancel (a := y*HaarCycle.norm x y z (P16 i))
      rw [← normShiftY x y z cx cy rel,hn,normShiftY x y z cx cy rel,←hn]
    · exfalso
      apply Y
      have hp : z^(-(P16 j).2.1) = z^(-(P16 i).2.1) := by
        apply mul_left_cancel (a := x*HaarCycle.norm x y z (P16 j))
        rw [← normShiftX x y z cx cy rel,←hn,normShiftX x y z cx cy rel,hn]
      have h := power_even z h1 h2 hp
      convert h using 2 <;> ring
    · obtain ⟨e1,e2,e3⟩ := H
      unfold HaarCycle.norm at hn
      rw [e1,e2] at hn
      have hp := mul_left_cancel hn
      rcases e3 with r | r
      · have h := power_even z h1 h2 hp; omega
      · have h := power_even z h1 h2 hp.symm; omega
    · exact False.elim (hv (offset_fourth x y z cx cy rel h2 _ _ H.1 H.2 hn))
    · exact False.elim (hv (offset_fourth x y z cx cy rel h2 _ _ H.1 H.2 hn.symm))

end HaarOrderTwo

#print axioms HaarOrderTwo.choose
