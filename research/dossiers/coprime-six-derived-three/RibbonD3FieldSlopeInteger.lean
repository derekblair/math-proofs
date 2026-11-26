import RibbonD3FieldSlopeCore

namespace RibbonD3Field
open RibbonAffine (pl mon)
open RibbonStationaryField (Id Branch Poly natConst binom)
variable {K : Type*} [Field K]

structure IntRow where
  n : Int
  witness : Id
  deriving Inhabited

structure IntCover where
  constant : Int
  powers : Nat × Nat
  primes : List Nat
  rows : Array IntRow
  deriving Inhabited

def integerValid (f : Poly) (G : SlopeGeom) (C : IntCover) : Prop :=
  C.constant.natAbs = 2^C.powers.1*3^C.powers.2*C.primes.prod ∧
  ∀ i : Fin G.rows.size,
    let r := G.rows[i]
    let w := C.rows[i.val]!
    w.n ∣ C.constant ∧ w.witness.rhs=natConst w.n ∧
      w.witness.valid f r.trans (binom r.exponent) 0
instance (f : Poly) (G : SlopeGeom) (C : IntCover) : Decidable (integerValid f G C) := by
  unfold integerValid
  infer_instance

theorem int_zero_primes (c : Int) (x y : Nat) (P : List Nat)
    (w : c.natAbs=2^x*3^y*P.prod) (two : (2:K)≠0) (three : (3:K)≠0) (Z : (c:K)=0) :
    ∃ p ∈ P, ((p:Nat):K)=0 := by
  have Y : (c.natAbs:K)=0 := by
    by_cases p : 0≤c
    · rw [←Int.cast_natCast,Int.natAbs_of_nonneg p]
      exact Z
    · rw [←Int.cast_natCast,show (c.natAbs:Int) = -c by omega,Int.cast_neg,Z,neg_zero]
  rw [w,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow] at Y
  have Q : (P.prod:K)=0 := (mul_eq_zero.mp Y).resolve_left
    (mul_ne_zero (pow_ne_zero _ (by simpa using two)) (pow_ne_zero _ (by simpa using three)))
  rw [Nat.cast_list_prod] at Q
  obtain ⟨p,h,z⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp Q)
  exact ⟨p,h,z⟩

theorem integer_cover (f : Poly) (G : SlopeGeom) (C : IntCover) (u v : Int)
    (GV : GeomValid G u v) (V : integerValid f G C)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1)
    (two : (2:K)≠0) (three : (3:K)≠0) (F : pl t 1 f=0) :
    Ordered (chart G.word) (t^v) (t^(-u)) ∨ ∃ p∈C.primes, (p:K)=0 := by
  classical
  by_cases O : Ordered (chart G.word) (t^v) (t^(-u))
  · exact Or.inl O
  right
  unfold Ordered at O
  push_neg at O
  obtain ⟨i,j,l,E⟩ := O
  obtain ⟨s,T,N⟩ := geometry_sound G u v GV t n odd no3 tn t1 i j l E
  obtain ⟨d,h,I⟩ := V.2 s
  have z := (C.rows[s.val]!).witness.sound f _ _ 0 I t F T N (by simp)
  rw [h] at z
  have zz : ((C.rows[s.val]!).n:K)=0 := by simpa [natConst,pl,mon] using z
  obtain ⟨c,e⟩ := d
  apply int_zero_primes C.constant C.powers.1 C.powers.2 _ V.1 two three
  rw [e,Int.cast_mul,zz,zero_mul]

end RibbonD3Field
#print axioms RibbonD3Field.integer_cover
