import HaarP3CharExceptional
import HaarP3CollectActions

namespace HaarP3FifthCharacter
open HaarP3Char HaarP3CollectActions
variable {G : Type*} [Group G]

def digit (w : C3) : ℤ := w.toAdd.val

theorem digit_range (w : C3) : 0≤digit w ∧ digit w<3 := by
  have := ZMod.val_lt w.toAdd
  unfold digit
  omega

theorem digit_cast (w : C3) : ((digit w : ℤ) : ZMod 3)=w.toAdd := by
  unfold digit
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem digit_injective : Function.Injective digit := by
  intro a b e
  change a.toAdd=b.toAdd
  rw [← digit_cast a,← digit_cast b,e]

theorem digit_zero : digit (1:C3)=0 := by decide +kernel

theorem unit_digit (w : C3) :
    digit w=0 ∨ digit w=1 ∨ digit w=2 := by
  have := digit_range w
  omega

theorem digit_pow (z w : C3) (hz : digit z=1) : z^digit w=w := by
  have finite : ∀ a b : C3, digit a=1 → a^digit b=b := by decide +kernel
  exact finite z w hz

theorem invdigit : ∀ w : C3, (digit w=1 → digit w⁻¹=2) ∧
    (digit w=2 → digit w⁻¹=1) := by decide +kernel

theorem choose_generator {S : Subgroup G} (χ : S→*C3) (nc : χ≠1) :
    ∃ z : S, digit (χ z)=1 := by
  classical
  by_contra! none
  apply nc
  ext w
  change χ w=1
  rcases unit_digit (χ w) with h|h|h
  · exact digit_injective (h.trans digit_zero.symm)
  · exact (none w h).elim
  · have hv : digit (χ (w⁻¹))=1 := by rw [map_inv]; exact (invdigit (χ w)).2 h
    exact (none w⁻¹ hv).elim

def parameters {S : Subgroup G} (χ : S→*C3) (p q a b c : S) : Params :=
  ⟨digit (χ p),digit (χ q),digit (χ a),digit (χ b),digit (χ c)⟩

theorem mapped_power {S : Subgroup G} (central : S≤Subgroup.center G) (χ : S→*C3) (z w : S)
    (hz : digit (χ z)=1) :
    let N := centralKernel S χ
    letI : N.Normal := kernel_normal central χ
    let π := QuotientGroup.mk' N
    π w.val = (π z.val)^digit (χ w) := by
  let N := centralKernel S χ
  let : N.Normal := kernel_normal central χ
  let π := QuotientGroup.mk' N
  change π w.val=(π z.val)^digit (χ w)
  rw [← map_zpow]
  apply (quotient_detects_char central χ w (z^digit (χ w))).mpr
  rw [map_zpow,digit_pow (χ z) _ hz]

theorem exceptional_digits {p q a b c : C3}
    (h : (digit p=1 ∧ digit q=2 ∧ digit a=2 ∧ digit b=2 ∧ digit c=2) ∨
         (digit p=2 ∧ digit q=1 ∧ digit a=1 ∧ digit b=1 ∧ digit c=1)) :
    q=p⁻¹ ∧ a=p⁻¹ ∧ b=p⁻¹ ∧ c=p⁻¹ := by
  rcases h with ⟨p1,q2,a2,b2,c2⟩ | ⟨p2,q1,a1,b1,c1⟩
  · have e := (invdigit p).1 p1
    exact ⟨digit_injective (q2.trans e.symm),digit_injective (a2.trans e.symm),
      digit_injective (b2.trans e.symm),digit_injective (c2.trans e.symm)⟩
  · have e := (invdigit p).2 p2
    exact ⟨digit_injective (q1.trans e.symm),digit_injective (a1.trans e.symm),
      digit_injective (b1.trans e.symm),digit_injective (c1.trans e.symm)⟩

end HaarP3FifthCharacter
#print axioms HaarP3FifthCharacter.mapped_power
#print axioms HaarP3FifthCharacter.exceptional_digits

namespace HaarP3FifthCharacter
open HaarP3Char
variable {G : Type*} [Group G]

theorem not_both_zero {S : Subgroup G} (χ : S→*C3) (nc : χ≠1) (p q : S)
    (gen : S=Subgroup.closure ({p.val,q.val} : Set G)) :
    ¬(digit (χ p)=0 ∧ digit (χ q)=0) := by
  rintro ⟨hp,hq⟩
  apply nc
  have H : S≤centralKernel S χ := by
    refine (le_of_eq gen).trans ?_
    apply (Subgroup.closure_le _).mpr
    intro a h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact (mem_kernel_iff χ p.property).mpr (digit_injective (hp.trans digit_zero.symm))
    · exact (mem_kernel_iff χ q.property).mpr (digit_injective (hq.trans digit_zero.symm))
  ext w
  change χ w=1
  exact (mem_kernel_iff χ w.property).mp (H w.property)

end HaarP3FifthCharacter
#print axioms HaarP3FifthCharacter.not_both_zero
