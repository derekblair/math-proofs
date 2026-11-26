import HaarAllNoncommuting

namespace HaarBound16
open HaarCycle HaarOrderTwo HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem raw16 (i j : Fin 16) :
    i=j ∨ side16 i ≠ side16 j ∨
    let p := P16 i; let q := P16 j
    (abs (p.1-q.1) ≤ 3 ∧ abs (p.2.1-q.2.1) ≤ 3 ∧
    (p.1=q.1 → p.2.1=q.2.1 → (p.2.2-q.2.2=1 ∨ q.2.2-p.2.2=1))) := by
  revert i j
  decide

theorem inject_bound (z : G) (h1 : z≠1) (h2 : z^2≠1) (h3 : z^3≠1) {m n : ℤ}
    (bound : abs (m-n)≤3) (eq : z^m=z^n) : m=n := by
  by_contra hn
  have B := abs_le.mp bound
  have h (a b : ℤ) (hk : z^a=z^b) : z^(a-b)=1 := by rw [zpow_sub,hk,mul_inv_cancel]
  have k (a b : ℤ) (hk : z^a=z^b) (it : a-b=1 ∨ a-b=2 ∨ a-b=3) : False := by
    have he := h a b hk
    rcases it with r|r|r
    · exact h1 (by simpa [r] using he)
    · exact h2 (by simpa [r] using he)
    · exact h3 (by simpa [r] using he)
  by_cases HH : m>n
  · exact k m n eq (by omega)
  · exact k n m eq.symm (by omega)

theorem conjugate_eq (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) {p q : Coord}
    (hh : HaarCycle.norm x y z p=HaarCycle.norm x y z q) :
    z^p.1=z^q.1 ∧ z^p.2.1=z^q.2.1 := by
  constructor
  · apply mul_left_cancel (a:=y*HaarCycle.norm x y z p)
    rw [←normShiftY x y z cx cy rel,hh,normShiftY x y z cx cy rel,←hh]
  · have h : z^(-p.2.1)=z^(-q.2.1) := by
      apply mul_left_cancel (a:=x*HaarCycle.norm x y z p)
      rw [←normShiftX x y z cx cy rel,hh,normShiftX x y z cx cy rel,←hh]
    simpa using h

theorem ge4 (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) (h2 : z^2≠1) (h3 : z^3≠1) :
    HasCycle x y 16 := by
  apply cycle_form (v16 x y z) _ (adj16 x y z cx cy rel)
  intro i j he
  have hh := congrArg Prod.snd he
  change HaarCycle.norm x y z (P16 i)=HaarCycle.norm x y z (P16 j) at hh
  rcases raw16 i j with h | h | ⟨d1,d2,e⟩
  · exact h
  · exact False.elim (h (congrArg Prod.fst he))
  · obtain ⟨hx,hy⟩ := conjugate_eq x y z cx cy rel hh
    have hX := inject_bound z h1 h2 h3 d1 hx
    have hY := inject_bound z h1 h2 h3 d2 hy
    have hp := e hX hY
    unfold HaarCycle.norm at hh
    rw [hX,hY] at hh
    have ek := mul_left_cancel hh
    exact False.elim ((centralNE z h1 h2 _ _ (by omega)) ek)

def P3 : Fin 16 → Coord := fun i => (#[ (0,0,0), (0,0,0), (-1,0,0), (-1,0,0),
  (-2,0,0), (-2,1,-2), (-2,1,-2), (-1,1,-2),
  (-1,1,-2), (0,1,-2), (0,0,-2), (0,0,-2),
  (-1,0,-2), (-1,1,-3), (-1,1,-3), (0,1,-3)] : Array Coord)[i.val]!

def close (p q : Coord) : Prop := p.1=q.1 ∧ p.2.1=q.2.1 ∧ (p.2.2-q.2.2)%3=0

instance (p q : Coord) : Decidable (close p q) := by unfold close; infer_instance

theorem e3match (i : Fin 16) :
    let p := if side16 i then P3 (i+1) else P3 i
    let q := if side16 i then P3 i else P3 (i+1)
    close q p ∨ close q (rightX p) ∨ close q (rightY p) := by
  revert i
  decide

theorem sep3 (i j : Fin 16) :
    i=j ∨ side16 i≠side16 j ∨ ¬ close (P3 i) (P3 j) := by
  revert i j
  decide

theorem raw3 (i j : Fin 16) :
    abs ((P3 i).1-(P3 j).1) ≤ 2 ∧ abs ((P3 i).2.1-(P3 j).2.1) ≤ 2 := by
  revert i j
  decide

theorem pow_mod_three (z : G) (h : z^3=1) {a b : ℤ} (eq : (a-b)%3=0) :
    z^a=z^b := by
  have e : a-b=3*((a-b)/3) := by omega
  have ez : z^(3:ℤ)=1 := by exact_mod_cast h
  have hz : z^(a-b)=1 := by rw [e,zpow_mul,ez,one_zpow]
  have hh := congrArg (fun x => x * z^b) hz
  simpa [zpow_sub,mul_assoc] using hh

theorem oneTwo (z : G) (h1 : z≠1) (h3 : z^3=1) : z^2≠1 := by
  intro hz
  have h : z^3=z := by rw [show 3=2+1 by decide,pow_succ,hz,one_mul]
  exact h1 (h.symm.trans h3)

theorem pow_eq_mod_three (z : G) (h1 : z≠1) (h3 : z^3=1) {a b : ℤ} (eq : z^a=z^b) :
    (a-b)%3=0 := by
  have h : z^(a-b)=1 := by rw [zpow_sub,eq,mul_inv_cancel]
  let r := (a-b)%3
  have hr : z^(a-b)=z^r := pow_mod_three z h3 (show (a-b-r)%3=0 by dsimp [r]; omega)
  rw [hr] at h
  have bounds : 0≤r ∧ r<3 := by dsimp [r]; omega
  have h2 := oneTwo z h1 h3
  have e : r=0 ∨ r=1 ∨ r=2 := by omega
  rcases e with e|e|e
  · exact e
  · exact False.elim (h1 (by simpa [e] using h))
  · exact False.elim (h2 (by simpa [e] using h))

theorem order3 (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) (h3 : z^3=1) :
    HasCycle x y 16 := by
  let V : Fin 16 → Bool×G := fun i => (side16 i,HaarCycle.norm x y z (P3 i))
  apply cycle_form V
  · intro i j e
    have hh : HaarCycle.norm x y z (P3 i)=HaarCycle.norm x y z (P3 j) := congrArg Prod.snd e
    rcases sep3 i j with h|h|h
    · exact h
    · exact False.elim (h (congrArg Prod.fst e))
    · exfalso
      apply h
      obtain ⟨px,py⟩ := conjugate_eq x y z cx cy rel hh
      obtain ⟨b1,b2⟩ := raw3 i j
      have h2 := oneTwo z h1 h3
      have X := from_bounded_eq z h1 h2 b1 px
      have Y := from_bounded_eq z h1 h2 b2 py
      refine ⟨X,Y,pow_eq_mod_three z h1 h3 ?_⟩
      unfold HaarCycle.norm at hh
      rw [X,Y] at hh
      exact mul_left_cancel hh
  · intro i
    have he (p q : Coord) (hp : close p q) :
        HaarCycle.norm x y z p=HaarCycle.norm x y z q := by
      obtain ⟨a,b,c⟩ := hp
      unfold HaarCycle.norm
      rw [a,b,pow_mod_three z h3 c]
    have tr (p q : Coord) (hp : close q p ∨ close q (rightX p) ∨ close q (rightY p)) :
        HaarCycle.norm x y z q=HaarCycle.norm x y z p ∨
        HaarCycle.norm x y z q=HaarCycle.norm x y z p*x ∨
        HaarCycle.norm x y z q=HaarCycle.norm x y z p*y := by
      rcases hp with hp|hp|hp
      · exact Or.inl (he _ _ hp)
      · exact Or.inr (Or.inl ((he _ _ hp).trans (normX x y z cx p)))
      · exact Or.inr (Or.inr ((he _ _ hp).trans (normY x y z cx cy rel p)))
    have hs := (cert16 i).1
    have cert := e3match i
    cases hi : side16 i <;> cases hj : side16 (i+1) <;> simp [hi,hj] at hs cert
    · simpa [V,haarAdj,hi,hj] using tr _ _ cert
    · simpa [V,haarAdj,hi,hj] using tr _ _ cert

theorem sharpened (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z≠1) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 := by
  have xy : x ≠ y := by
    rintro rfl
    exact h1 (mul_left_cancel (rel.symm.trans (mul_one _).symm))
  by_cases h2 : z^2=1
  · rcases choose x y z cx cy rel h1 h2 with ha | hb
    · exact Or.inr (Or.inr (cycle_form _ ha (adj16 x y z cx cy rel)))
    · rcases fourth x y xy hb with ⟨v,a,b⟩ | ⟨v,a,b⟩
      · exact Or.inl (cycle_form v a b)
      · exact Or.inr (Or.inl (cycle_form v a b))
  · by_cases h3 : z^3=1
    · exact Or.inr (Or.inr (order3 x y z cx cy rel h1 h3))
    · exact Or.inr (Or.inr (ge4 x y z cx cy rel h1 h2 h3))

end HaarBound16
#print axioms HaarBound16.sharpened
