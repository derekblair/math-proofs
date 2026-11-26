import HaarP3Class4Cases
import HaarClass4Projection

namespace HaarP3Class4Interpret
open HaarP3Class4Cases HaarClass4Normal
variable {G H : Type*} [Group G] [Group H]

def tailValue (M : Data G) (a : Coeff) :=
  M.u^a.1 * M.v^a.2.1 * M.a^a.2.2.1 * M.b^a.2.2.2.1 * M.d^a.2.2.2.2

theorem order_mod {g : G} (ord : 3 ∣ orderOf g) {n : ℤ} (h : g^n=1) :
    n%3=0 := by
  have d : (3:ℤ) ∣ (orderOf g:ℤ) := by exact_mod_cast ord
  exact Int.emod_eq_zero_of_dvd (d.trans (orderOf_dvd_iff_zpow_eq_one.mpr h))

theorem pivot_detect (φ : G →* H) (w a : G) (e : ℕ)
    (ha : orderOf a=3) (hk : φ a=1) (hw : 3 ∣ orderOf (φ w))
    (cube : w^(3:ℕ)=a^e) (u v : ℤ) (he : w^u*a^v=1) :
    u%3=0 ∧ (v+(u/3)*(e:ℤ))%3=0 := by
  have x := congrArg φ he
  simp only [map_mul,map_zpow,map_one,hk,one_zpow,mul_one] at x
  have h0 : u%3=0 := order_mod hw x
  have fe : w^u=a^((u/3)*(e:ℤ)) := by
    conv_lhs => rw [show u=3*(u/3) by omega]
    rw [zpow_mul,show w^(3:ℤ)=a^(e:ℤ) by exact_mod_cast cube,←zpow_mul,mul_comm (e:ℤ)]
  rw [fe,←zpow_add,add_comm] at he
  exact ⟨h0,order_mod (by rw [ha]) he⟩

def firstAxis (j : Fin 3) : Fin 4 := ⟨j.val, by omega⟩

theorem value_U (M : Data G) (j t : Fin 3) (a : Coeff)
    (hv : M.v=M.u^j.val*M.a^t.val) (hb : M.b=M.a^j.val)
    (hd : M.d=M.a^(j.val*j.val)) :
    tailValue M a = M.u^(lead (firstAxis j) a) *
        M.a^(a.2.2.1+(j.val:ℤ)*a.2.2.2.1+(j.val:ℤ)*(j.val:ℤ)*a.2.2.2.2+(t.val:ℤ)*a.2.1) := by
  have c := (M.ca M.u).symm.zpow_zpow (j.val:ℤ) (t.val:ℤ)
  have dj : (firstAxis j).val<3 := j.isLt
  unfold tailValue lead
  rw [if_pos dj,hv,hb,hd]
  simp only [firstAxis] at *
  simp only [← zpow_natCast, Nat.cast_mul, c.mul_zpow, ← zpow_mul]
  group
  <;> ring_nf

theorem value_V (M : Data G) (t : Fin 3) (a : Coeff)
    (hu : M.u=M.d^t.val) (ha : M.a=1) (hb : M.b=1) :
    tailValue M a = M.v^(lead 3 a) * M.d^(a.2.2.2.2+(t.val:ℤ)*a.1) := by
  unfold tailValue lead
  rw [if_neg (by decide),hu,ha,hb]
  simp only [one_zpow,mul_one,←zpow_natCast,←zpow_mul]
  rw [((M.cd M.v).zpow_zpow ((t.val:ℤ)*a.1) a.2.1).eq]
  simp only [mul_assoc,←zpow_add]
  rw [add_comm ((t.val:ℤ)*a.1)]

theorem detect_U (M : Data G) (φ : G →* H) (j t e : Fin 3) (a : Coeff)
    (hao : orderOf M.a=3) (hk : φ M.a=1) (hw : 3 ∣ orderOf (φ M.u))
    (hv : M.v=M.u^j.val*M.a^t.val) (hb : M.b=M.a^j.val)
    (hd : M.d=M.a^(j.val*j.val)) (cu : M.u^(3:ℕ)=M.a^e.val)
    (h : tailValue M a=1) :
    lead (firstAxis j) a%3=0 ∧ rem4 (firstAxis j) t e a%3=0 := by
  rw [value_U M j t a hv hb hd] at h
  have d := pivot_detect φ M.u M.a e.val hao hk hw cu _ _ h
  simpa [rem4,firstAxis,j.isLt] using d

theorem detect_V (M : Data G) (φ : G →* H) (t e : Fin 3) (a : Coeff)
    (hao : orderOf M.d=3) (hk : φ M.d=1) (hw : 3 ∣ orderOf (φ M.v))
    (hu : M.u=M.d^t.val) (ha : M.a=1) (hb : M.b=1)
    (cv : M.v^(3:ℕ)=M.d^e.val) (h : tailValue M a=1) :
    lead 3 a%3=0 ∧ rem4 3 t e a%3=0 := by
  rw [value_V M t a hu ha hb] at h
  have d := pivot_detect φ M.v M.d e.val hao hk hw cv _ _ h
  simpa [rem4,show ¬ (3:Fin 4).val<3 by decide] using d

end HaarP3Class4Interpret
#print axioms HaarP3Class4Interpret.detect_U
#print axioms HaarP3Class4Interpret.detect_V
