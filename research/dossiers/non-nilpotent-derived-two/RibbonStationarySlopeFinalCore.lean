import RibbonStationaryModular
import RibbonStationaryExtras

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def FieldResidual (a b : Kˣ) : Prop :=
  (11:K)=0 ∧ (a:K)≠1 ∧
    ((a:K)=3 ∨ (a:K)=4 ∨ (a:K)=5 ∨ (a:K)=9) ∧
    ((b:K)=1 ∨ (b:K)=3 ∨ (b:K)=4 ∨ (b:K)=5 ∨ (b:K)=9)

theorem slope_use (B : Branch) (C : Cover) (T : RowValid B.p C) (G : GeomValid B C)
    (p : ∀ k : Fin C.rows.size, ∃ r : PrimeCert, primeValid B.p C.rows[k] r)
    (t : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (tn : t^n=1) (nt : t≠1) (F : pl t 1 B.p=0) :
    separates (t^B.v) (t^(-B.u)) C.k ∨
      ((11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9)) := by
  classical
  by_cases S : separates (t^B.v) (t^(-B.u)) C.k
  · exact Or.inl S
  right
  unfold separates at S
  push_neg at S
  obtain ⟨i,j,l,eq,h⟩ := S
  obtain ⟨r,H,M,N⟩ := (no_fallback_collision B C T G t n odd no3 tn nt F i j l eq).resolve_left h
  obtain ⟨pc,V⟩ := p r
  exact prime_sound t n odd no3 tn two B.p C.rows[r] pc V F H M N

theorem pow5_f11 (t : Kˣ) (p : (11:K)=0) (ht : (t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9) : t^5=1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val,Units.val_one]
  rcases ht with h|h|h|h <;> rw [h]
  · linear_combination 22*p
  · linear_combination 93*p
  · linear_combination 284*p
  · linear_combination 5368*p

theorem all5_field (a : Kˣ) (p : (11:K)=0) (h : a^5=1) :
    (a:K)=1 ∨ (a:K)=3 ∨ (a:K)=4 ∨ (a:K)=5 ∨ (a:K)=9 := by
  have c : (a:K)^5=1 := by simpa using congrArg (fun u : Kˣ => (u:K)) h
  have f : ((a:K)-1)*((a:K)-3)*((a:K)-4)*((a:K)-5)*((a:K)-9)=0 := by
    linear_combination c + (-(2:K)*(a:K)^4 + 16*(a:K)^3 - 58*(a:K)^2 + 93*(a:K) - 49)*p
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using f

theorem residual_from_t (t a b : Kˣ) (u v : Int)
    (hA : a=t^v) (hB : b=t^(-u)) (a1 : a≠1)
    (S : (11:K)=0 ∧ ((t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9)) :
    FieldResidual a b := by
  have h := pow5_f11 t S.1 S.2
  have a5 : a^5=1 := by
    rw [hA,←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul,zpow_natCast,h,one_zpow]
  have b5 : b^5=1 := by
    rw [hB,←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul,zpow_natCast,h,one_zpow]
  have x : (a:K)≠1 := fun z => a1 (Units.ext z)
  exact ⟨S.1,x,(all5_field a S.1 a5).resolve_left x,all5_field b S.1 b5⟩

end RibbonStationaryField
#print axioms RibbonStationaryField.slope_use
#print axioms RibbonStationaryField.residual_from_t
