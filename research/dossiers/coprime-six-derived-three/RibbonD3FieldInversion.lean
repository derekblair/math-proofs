import RibbonD3InvertData
import RibbonD3FieldOutcome

namespace RibbonD3Field
open RibbonAffine (pl)
variable {K : Type*} [Field K]
set_option maxHeartbeats 0
set_option maxRecDepth 30000

theorem exact_bad_inv (p : Nat) (Q : p=11 ∨ p=23 ∨ p=29) (x y : ZMod p)
    (H : (p,x.val,y.val)∈exactBad) :
    (p,(x⁻¹).val,y.val)∈exactBad ∧ (p,x.val,(y⁻¹).val)∈exactBad := by
  rcases Q with rfl|rfl|rfl
  · have C : (exactBad.all fun r => if r.1=11 then decide (
        (11,((r.2.1:ZMod 11)⁻¹).val,r.2.2)∈exactBad ∧
        (11,r.2.1,((r.2.2:ZMod 11)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (11,((x.val:ZMod 11)⁻¹).val,y.val)∈exactBad ∧
        (11,x.val,((y.val:ZMod 11)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=23 then decide (
        (23,((r.2.1:ZMod 23)⁻¹).val,r.2.2)∈exactBad ∧
        (23,r.2.1,((r.2.2:ZMod 23)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (23,((x.val:ZMod 23)⁻¹).val,y.val)∈exactBad ∧
        (23,x.val,((y.val:ZMod 23)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=29 then decide (
        (29,((r.2.1:ZMod 29)⁻¹).val,r.2.2)∈exactBad ∧
        (29,r.2.1,((r.2.2:ZMod 29)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (29,((x.val:ZMod 29)⁻¹).val,y.val)∈exactBad ∧
        (29,x.val,((y.val:ZMod 29)⁻¹).val)∈exactBad)

theorem prime_of_bad (p : Nat) (Q : p=11 ∨ p=23 ∨ p=29) : p.Prime := by
  rcases Q with rfl|rfl|rfl <;> decide

theorem field_bad_inv_left (a b : Kˣ) (W : FieldBad a⁻¹ b) : FieldBad a b := by
  obtain ⟨p,P,f,x,y,X,Y,Q⟩ := W
  letI : Fact p.Prime := ⟨prime_of_bad p P⟩
  refine ⟨p,P,f,x⁻¹,y,?_,Y,(exact_bad_inv p P x y Q).1⟩
  rw [map_inv₀,X,Units.val_inv_eq_inv_val,inv_inv]

theorem field_bad_inv_right (a b : Kˣ) (W : FieldBad a b⁻¹) : FieldBad a b := by
  obtain ⟨p,P,f,x,y,X,Y,Q⟩ := W
  letI : Fact p.Prime := ⟨prime_of_bad p P⟩
  refine ⟨p,P,f,x,y⁻¹,X,?_,(exact_bad_inv p P x y Q).2⟩
  rw [map_inv₀,Y,Units.val_inv_eq_inv_val,inv_inv]

def InvertedSeparates (a b : Kˣ) : Prop :=
  ∃ (invertX invertY : Bool) (k : Count), (if invertX then a⁻¹ else a)≠1 ∧
    Separates (chart k) (if invertX then a⁻¹ else a) (if invertY then b⁻¹ else b)

/-- A complete field classifier using at most one rim inversion. No special
surface-case certificate is an assumption of this theorem. -/
theorem inversion_cover (a b : Kˣ) (n : Nat)
    (odd : Odd n) (no3 : ¬3∣n) (two : (2:K)≠0) (three : (3:K)≠0)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) :
    InvertedSeparates a b ∨ FieldBad a b := by
  classical
  by_cases H : ∀ c : Int, surfaceIndex c → pl a b (surfacePoly c)≠0
  · rcases field_outside_surfaces a b n odd no3 two three an bn a1 H with ⟨k,S⟩|F
    · exact Or.inl ⟨false,false,k,a1,S⟩
    · exact Or.inr F
  push Not at H
  obtain ⟨c,C,H⟩ := H
  have av : (a⁻¹)^n=1 := by rw [inv_pow,an,inv_one]
  have bv : (b⁻¹)^n=1 := by rw [inv_pow,bn,inv_one]
  have ai : a⁻¹≠1 := by simpa using a1
  by_cases L : ∀ d : Int, surfaceIndex d → pl a⁻¹ b (surfacePoly d)≠0
  · rcases field_outside_surfaces a⁻¹ b n odd no3 two three av bn ai L with ⟨k,S⟩|F
    · exact Or.inl ⟨true,false,k,ai,S⟩
    · exact Or.inr (field_bad_inv_left a b F)
  push Not at L
  obtain ⟨d,D,L⟩ := L
  by_cases M : ∀ e : Int, surfaceIndex e → pl a b⁻¹ (surfacePoly e)≠0
  · rcases field_outside_surfaces a b⁻¹ n odd no3 two three an bv a1 M with ⟨k,S⟩|F
    · exact Or.inl ⟨false,true,k,a1,S⟩
    · exact Or.inr (field_bad_inv_right a b F)
  push Not at M
  obtain ⟨e,E,M⟩ := M
  exact Or.inr (field_bad_embed a b (invert_surfaces_bad c d e C D E a b H L M a1 two three n odd no3 an bn))

end RibbonD3Field
#print axioms RibbonD3Field.inversion_cover
