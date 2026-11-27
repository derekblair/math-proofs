import RibbonD3WideSlopeCore
import RibbonD3FieldSlopeInteger

namespace RibbonD3Wide
open RibbonD3Field
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
instance wideSlopeIntegerInst1 (f : Poly) (G : SlopeGeom) (C : IntCover) : Decidable (integerValid f G C) := by
  unfold integerValid
  infer_instance

theorem integer_cover (f : Poly) (G : SlopeGeom) (C : IntCover) (u v : Int)
    (GV : GeomValid G u v) (V : integerValid f G C)
    (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1) (t1 : t≠1)
    (two : (2:K)≠0) (three : (3:K)≠0) (F : pl t 1 f=0) :
    Ordered (chart G.word) (t^v) (t^(-u)) ∨ ∃ p∈C.primes, (p:K)=0 := by
  classical
  by_cases O : Ordered (chart G.word) (t^v) (t^(-u))
  · exact Or.inl O
  right
  unfold Ordered at O
  push_neg at O
  obtain ⟨i,j,l,E⟩ := O
  obtain ⟨s,T,N⟩ := geometry_sound G u v GV t n odd tn t1 i j l E
  obtain ⟨d,h,I⟩ := V.2 s
  have z := (C.rows[s.val]!).witness.sound f _ _ 0 I t F T N (by simp)
  rw [h] at z
  have zz : ((C.rows[s.val]!).n:K)=0 := by simpa [natConst,pl,mon] using z
  obtain ⟨c,e⟩ := d
  apply int_zero_primes C.constant C.powers.1 C.powers.2 _ V.1 two three
  rw [e,Int.cast_mul,zz,zero_mul]

end RibbonD3Wide
#print axioms RibbonD3Wide.integer_cover
