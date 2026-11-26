import HaarP3Char

namespace HaarP3Char
open HaarClass4Structure HaarP3LayerGen
variable {G : Type*} [Group G]

def centralKernel (S : Subgroup G) (χ : S →* C3) : Subgroup G := χ.ker.map S.subtype

theorem centralKernel_le (S : Subgroup G) (χ : S →* C3) : centralKernel S χ ≤ S := by
  rintro z ⟨w,hw,rfl⟩
  exact w.property

theorem kernel_normal {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (χ : S →* C3) : (centralKernel S χ).Normal :=
  Subgroup.normal_of_le_center ((centralKernel_le S χ).trans central)

theorem mem_kernel_iff {S : Subgroup G} (χ : S →* C3) {w : G} (hw : w∈S) :
    w ∈ centralKernel S χ ↔ χ ⟨w,hw⟩ = 1 := by
  constructor
  · rintro ⟨a,ha,e⟩
    have ea : a=⟨w,hw⟩ := Subtype.ext e
    exact ea ▸ MonoidHom.mem_ker.mp ha
  · intro h
    exact ⟨⟨w,hw⟩,MonoidHom.mem_ker.mpr h,rfl⟩

theorem quotient_detects_char {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (χ : S →* C3) (a b : S) :
    let N := centralKernel S χ
    letI : N.Normal := kernel_normal central χ
    let π := QuotientGroup.mk' N
    π a.val = π b.val ↔ χ a = χ b := by
  let N := centralKernel S χ
  let : N.Normal := kernel_normal central χ
  let π := QuotientGroup.mk' N
  change π a.val=π b.val ↔ _
  have e : π a.val=π b.val ↔ π (a*b⁻¹ : S).val=1 := by
    change _ ↔ π (a.val*b.val⁻¹)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
  refine e.trans ((QuotientGroup.eq_one_iff (a*b⁻¹ : S).val).trans ?_)
  refine (mem_kernel_iff χ (a*b⁻¹ : S).property).trans ?_
  change χ (a*b⁻¹)=1 ↔ χ a=χ b
  rw [map_mul,map_inv,mul_inv_eq_one]

theorem quotient_separates_of_ne {S : Subgroup G} (central : S ≤ Subgroup.center G)
    (cube : ∀ w∈S, w^(3:ℕ)=1) {a b : S} (hne : a≠b) :
    ∃ χ : S →* C3, χ ≠ 1 ∧
      (let N := centralKernel S χ
       letI : N.Normal := kernel_normal central χ
       QuotientGroup.mk' N a.val ≠ QuotientGroup.mk' N b.val) := by
  have e : ¬ ∀ χ : S →* C3, χ≠1 → χ a=χ b :=
    fun ha => hne (separated_equal central cube a b ha)
  push Not at e
  obtain ⟨χ,nχ,hχ⟩ := e
  exact ⟨χ,nχ,fun h => hχ ((quotient_detects_char central χ a b).mp h)⟩

end HaarP3Char

#print axioms HaarP3Char.quotient_separates_of_ne
