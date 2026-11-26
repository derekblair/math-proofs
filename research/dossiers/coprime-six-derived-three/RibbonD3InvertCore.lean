import RibbonD3FieldOutside
import RibbonD3RationalCases
import RibbonD3FieldSurfaceCore

namespace RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]

def triValue (c d e : Int) : Int := (c+d)^2-e*c*d^2
def triPoint (c d : Int) : RationalPoint := ⟨d,c,c*d,c+d⟩

theorem surfaceCoeff_ne (c : Int) (C : surfaceIndex c) (two : (2:K)≠0) (three : (3:K)≠0) :
    (c:K)≠0 := by
  rcases C with h | h | h | h | h <;> subst c
  · norm_num; exact three
  · norm_num; exact two
  · norm_num
  · norm_num
  · norm_num; exact two

theorem invert_surfaces (c d e : Int) (C : surfaceIndex c) (D : surfaceIndex d)
    (a b : Kˣ) (H : pl a b (surfacePoly c)=0) (L : pl a⁻¹ b (surfacePoly d)=0)
    (M : pl a b⁻¹ (surfacePoly e)=0) (a1 : a≠1) (two : (2:K)≠0) (three : (3:K)≠0) :
    c≠d ∧ c≠ -d ∧ (triPoint c d).Rep a b ∧ (triValue c d e:K)=0 := by
  have cn := surfaceCoeff_ne c C two three
  have dn := surfaceCoeff_ne d D two three
  have H := surface_eq c a b H
  have L := surface_eq d a⁻¹ b L
  have M := surface_eq e a b⁻¹ M
  have An : (a:K)⁻¹*(a:K)=1 := inv_mul_cancel₀ (Units.ne_zero a)
  have Bn : (b:K)⁻¹*(b:K)=1 := inv_mul_cancel₀ (Units.ne_zero b)
  simp only [Units.val_inv_eq_inv_val] at L M
  have A : (a:K)*(c:K)=(d:K) := by
    linear_combination -H + (a:K)*L + ((d:K)-(b:K))*An
  have B : (b:K)*((c:K)+(d:K))=(c:K)*(d:K) := by
    linear_combination (c:K)*H + ((c:K)-(b:K))*A
  have S : (c:K)+(d:K)≠0 := by
    intro Z
    rw [Z,mul_zero] at B
    exact mul_ne_zero cn dn B.symm
  have dc : c≠d := by
    intro Q
    have X : (a:K)*(c:K)=1*(c:K) := by simpa [←Q] using A
    exact a1 (Units.ext (mul_right_cancel₀ cn X))
  have dc' : c≠ -d := by
    intro Q
    exact S (by simp [Q])
  have E : (a:K)+1=(e:K)*(a:K)*(b:K) := by
    linear_combination (b:K)*M - ((a:K)+1)*Bn
  have castZero : ((c:K)+(d:K))^2-(e:K)*(c:K)*(d:K)^2=0 := by
    have Z : ((c:K)+(d:K))^2=(e:K)*(c:K)*(d:K)^2 := calc
      _ = ((a:K)+1)*(c:K)*((c:K)+(d:K)) := by linear_combination -((c:K)+(d:K))*A
      _ = (e:K)*((a:K)*(c:K))*((b:K)*((c:K)+(d:K))) := by rw [E]; ring
      _ = _ := by rw [A,B]; ring
    exact sub_eq_zero.mpr Z
  exact ⟨dc,dc',⟨cn,by simpa only [triPoint,Int.cast_add] using S,A,by
    simpa only [triPoint,Int.cast_add,Int.cast_mul] using B⟩,by
      simpa only [triValue,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_pow] using castZero⟩

structure TriReceipt where
  strip : Nat × Nat
  primes : List Nat
  mods : List RatPrime
  deriving Inhabited

def TriReceipt.valid (c d e : Int) (Z : TriReceipt) : Prop :=
  (triValue c d e).natAbs=2^Z.strip.1*3^Z.strip.2*Z.primes.prod ∧
    (Z.primes.all fun p => decide (∃ i : Fin Z.mods.length, Z.mods[i].p=p ∧ Z.mods[i].valid (triPoint c d)))=true
instance triReceiptValidDecidable (c d e : Int) (Z : TriReceipt) : Decidable (Z.valid c d e) := by
  unfold TriReceipt.valid; infer_instance

theorem TriReceipt.sound (c d e : Int) (Z : TriReceipt) (V : Z.valid c d e)
    (a b : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (two : (2:K)≠0) (three : (3:K)≠0)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1)
    (R : (triPoint c d).Rep a b) (E : (triValue c d e:K)=0) :
    ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad := by
  obtain ⟨p,P,X⟩ := int_zero_primes _ _ _ _ V.1 two three E
  obtain ⟨i,HP,VP⟩ := of_decide_eq_true (List.all_eq_true.mp V.2 p P)
  exact Z.mods[i].sound (triPoint c d) VP a b R n odd no3 an bn a1 (by rwa [HP])

#print axioms RibbonD3Field.invert_surfaces
#print axioms RibbonD3Field.TriReceipt.sound
end RibbonD3Field
