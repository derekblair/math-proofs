import RibbonAllOddModular
import RibbonStationarySlopeFinalCore

namespace RibbonAllOddField
open RibbonStationaryField (Branch pow5_f11 all5_field)
variable {K : Type*} [Field K]

def Raw (p a b : Nat) : Prop :=
  (p=7 ∧ (a=2 ∨ a=4) ∧ (b=1 ∨ b=2 ∨ b=4)) ∨
  (p=11 ∧ (a=3 ∨ a=4 ∨ a=5 ∨ a=9) ∧ (b=1 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=9)) ∨
  (p=13 ∧ (a=3 ∨ a=9) ∧ (b=1 ∨ b=3 ∨ b=9)) ∨ (p=43 ∧ a=31 ∧ b=1)

instance (p a b : Nat) : Decidable (Raw p a b) := by unfold Raw; infer_instance

def FieldResidual (a b : Kˣ) : Prop :=
  ∃ p i j : Nat, (p:K)=0 ∧ (a:K)=(i:K) ∧ (b:K)=(j:K) ∧ Raw p i j

private theorem pow3_of7 (t : Kˣ) (p : (7:K)=0) (ht : (t:K)=2 ∨ (t:K)=4) : t^3=1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val,Units.val_one]
  rcases ht with h|h <;> rw [h]
  · linear_combination p
  · linear_combination 9*p

private theorem pow3_of13 (t : Kˣ) (p : (13:K)=0) (ht : (t:K)=3 ∨ (t:K)=9) : t^3=1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val,Units.val_one]
  rcases ht with h|h <;> rw [h]
  · linear_combination 2*p
  · linear_combination 56*p

private theorem all3_7 (a : Kˣ) (p : (7:K)=0) (h : a^3=1) : (a:K)=1 ∨ (a:K)=2 ∨ (a:K)=4 := by
  have c : (a:K)^3=1 := by simpa using congrArg (fun u : Kˣ => (u:K)) h
  have f : ((a:K)-1)*((a:K)-2)*((a:K)-4)=0 := by
    linear_combination c + (-(a:K)^2 + 2*(a:K) - 1)*p
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using f

private theorem all3_13 (a : Kˣ) (p : (13:K)=0) (h : a^3=1) : (a:K)=1 ∨ (a:K)=3 ∨ (a:K)=9 := by
  have c : (a:K)^3=1 := by simpa using congrArg (fun u : Kˣ => (u:K)) h
  have f : ((a:K)-1)*((a:K)-3)*((a:K)-9)=0 := by
    linear_combination c + (-(a:K)^2 + 3*(a:K) - 2)*p
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using f

private theorem powers (t : Kˣ) (e : Nat) (h : t^e=1) (s : Int) : (t^s)^e=1 := by
  rw [←zpow_natCast,←zpow_mul,Int.mul_comm,zpow_mul,zpow_natCast,h,one_zpow]

theorem residual_from_root (B : Branch) (t a b : Kˣ) (hA : a=t^B.v) (hB : b=t^(-B.u))
    (a1 : a≠1) (S : ResidueRoot B t) : FieldResidual a b := by
  have na : (a:K)≠1 := fun z => a1 (Units.ext z)
  obtain ⟨p,z,p0,tz,R⟩ := S
  rcases R with ⟨rfl,R⟩|⟨rfl,R⟩|⟨rfl,R⟩|⟨rfl,rfl,u,v⟩
  · have P : (7:K)=0 := by simpa using p0
    have T : (t:K)=2 ∨ (t:K)=4 := by rcases R with rfl|rfl <;> simp_all
    have q := pow3_of7 t P T
    have c := (all3_7 a P (hA ▸ powers t 3 q B.v)).resolve_left na
    have d := all3_7 b P (hB ▸ powers t 3 q (-B.u))
    have a_exists : ∃ z : Nat, (a:K)=(z:K) ∧ (z=2 ∨ z=4) := by
      rcases c with h|h
      · exact ⟨2,h,Or.inl rfl⟩
      · exact ⟨4,h,Or.inr (rfl)⟩
    have b_exists : ∃ z : Nat, (b:K)=(z:K) ∧ (z=1 ∨ z=2 ∨ z=4) := by
      rcases d with h|h|h
      · exact ⟨1,by simpa using h,Or.inl rfl⟩
      · exact ⟨2,h,Or.inr (Or.inl rfl)⟩
      · exact ⟨4,h,Or.inr (Or.inr (rfl))⟩
    obtain ⟨i,H,IH⟩ := a_exists
    obtain ⟨j,J,JH⟩ := b_exists
    exact ⟨7,i,j,p0,H,J,Or.inl ⟨rfl,IH,JH⟩⟩
  · have P : (11:K)=0 := by simpa using p0
    have T : (t:K)=3 ∨ (t:K)=4 ∨ (t:K)=5 ∨ (t:K)=9 := by
      rcases R with rfl|rfl|rfl|rfl <;> simp_all
    have q := pow5_f11 t P T
    have c := (all5_field a P (hA ▸ powers t 5 q B.v)).resolve_left na
    have d := all5_field b P (hB ▸ powers t 5 q (-B.u))
    have a_exists : ∃ z : Nat, (a:K)=(z:K) ∧ (z=3 ∨ z=4 ∨ z=5 ∨ z=9) := by
      rcases c with h|h|h|h
      · exact ⟨3,h,Or.inl rfl⟩
      · exact ⟨4,h,Or.inr (Or.inl rfl)⟩
      · exact ⟨5,h,Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨9,h,Or.inr (Or.inr (Or.inr (rfl)))⟩
    have b_exists : ∃ z : Nat, (b:K)=(z:K) ∧ (z=1 ∨ z=3 ∨ z=4 ∨ z=5 ∨ z=9) := by
      rcases d with h|h|h|h|h
      · exact ⟨1,by simpa using h,Or.inl rfl⟩
      · exact ⟨3,h,Or.inr (Or.inl rfl)⟩
      · exact ⟨4,h,Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨5,h,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨9,h,Or.inr (Or.inr (Or.inr (Or.inr (rfl))))⟩
    obtain ⟨i,H,IH⟩ := a_exists
    obtain ⟨j,J,JH⟩ := b_exists
    exact ⟨11,i,j,p0,H,J,Or.inr (Or.inl ⟨rfl,IH,JH⟩)⟩
  · have P : (13:K)=0 := by simpa using p0
    have T : (t:K)=3 ∨ (t:K)=9 := by rcases R with rfl|rfl <;> simp_all
    have q := pow3_of13 t P T
    have c := (all3_13 a P (hA ▸ powers t 3 q B.v)).resolve_left na
    have d := all3_13 b P (hB ▸ powers t 3 q (-B.u))
    have a_exists : ∃ z : Nat, (a:K)=(z:K) ∧ (z=3 ∨ z=9) := by
      rcases c with h|h
      · exact ⟨3,h,Or.inl rfl⟩
      · exact ⟨9,h,Or.inr (rfl)⟩
    have b_exists : ∃ z : Nat, (b:K)=(z:K) ∧ (z=1 ∨ z=3 ∨ z=9) := by
      rcases d with h|h|h
      · exact ⟨1,by simpa using h,Or.inl rfl⟩
      · exact ⟨3,h,Or.inr (Or.inl rfl)⟩
      · exact ⟨9,h,Or.inr (Or.inr (rfl))⟩
    obtain ⟨i,H,IH⟩ := a_exists
    obtain ⟨j,J,JH⟩ := b_exists
    exact ⟨13,i,j,p0,H,J,Or.inr (Or.inr (Or.inl ⟨rfl,IH,JH⟩))⟩
  · exact ⟨43,31,1,p0,by simpa [hA,v] using tz,by simp [hB,u],by decide⟩

end RibbonAllOddField
#print axioms RibbonAllOddField.residual_from_root
