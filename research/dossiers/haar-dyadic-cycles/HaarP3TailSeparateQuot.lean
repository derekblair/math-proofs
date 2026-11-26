import HaarP3TailSeparate
import HaarP3CharKernel

namespace HaarP3TailSeparate
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarP3LayerGen HaarP3Char
open HaarP3FifthCert HaarP3CollectActions HaarP3CollectCore

variable {G : Type*} [Group G]

theorem separates_char (nil : LS G 5=⊥) (x y : G) (Z : LS G 4)
    (χ : (LS G 4) →* C3) (χZ : χ Z≠1)
    (ordC : 3∣orderOf (QuotientGroup.mk' (LS G 2) (portC x y)))
    (ordU : 3∣orderOf (QuotientGroup.mk' (LS G 3) (portU x y)))
    (ordA : 3∣orderOf (QuotientGroup.mk' (LS G 4) ⁅portU x y,x⁆)) :
    let N := centralKernel (LS G 4) χ
    let : N.Normal := kernel_normal (ls4_center_of_class5 nil) χ
    let π := QuotientGroup.mk' N
    ∀ M : Model (G ⧸ N), M.x=π x → M.y=π y →
      M.C=π (portC x y) → M.U=π (portU x y) →
      M.A=π ⁅portU x y,x⁆ → M.Z=π Z.val → Separates M := by
  let S := LS G 4
  let N := centralKernel S χ
  let : N.Normal := kernel_normal (ls4_center_of_class5 nil) χ
  let π := QuotientGroup.mk' N
  change ∀ M : Model (G ⧸ N), M.x=π x → M.y=π y →
    M.C=π (portC x y) → M.U=π (portU x y) →
    M.A=π ⁅portU x y,x⁆ → M.Z=π Z.val → Separates M
  intro M hx hy hc hu ha hz
  let c := portC x y
  let u := portU x y
  let v := portV x y
  let A := ⁅u,x⁆
  have NS : N≤S := centralKernel_le S χ
  have anti := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)
  have n2 : N≤(LS G 2).comap (MonoidHom.id G) := NS.trans (anti (by decide : 2≤4))
  have n3 : N≤(LS G 3).comap (MonoidHom.id G) := NS.trans (anti (by decide : 3≤4))
  have n4 : N≤(LS G 4).comap (MonoidHom.id G) := NS
  let φ₂ := QuotientGroup.map N (LS G 2) (MonoidHom.id G) n2
  let φ₃ := QuotientGroup.map N (LS G 3) (MonoidHom.id G) n3
  let φ₄ := QuotientGroup.map N (LS G 4) (MonoidHom.id G) n4
  let m₂ := QuotientGroup.mk' (LS G 2)
  let m₃ := QuotientGroup.mk' (LS G 3)
  let m₄ := QuotientGroup.mk' (LS G 4)
  have p₂ (w : G) : φ₂ (π w)=m₂ w := QuotientGroup.map_mk' N _ _ _ _
  have p₃ (w : G) : φ₃ (π w)=m₃ w := QuotientGroup.map_mk' N _ _ _ _
  have p₄ (w : G) : φ₄ (π w)=m₄ w := QuotientGroup.map_mk' N _ _ _ _
  have u2 : m₂ u=1 := (QuotientGroup.eq_one_iff _).mpr (layer_u x y)
  have v2 : m₂ v=1 := (QuotientGroup.eq_one_iff _).mpr (layer_v x y)
  have a3 : A∈LS G 3 := next_layer (layer_u x y) x
  have a2 : m₂ A=1 := (QuotientGroup.eq_one_iff _).mpr (anti (by decide : 2≤3) a3)
  have z2 : m₂ Z.val=1 := (QuotientGroup.eq_one_iff _).mpr
    (anti (by decide : 2≤4) Z.property)
  have a3' : m₃ A=1 := (QuotientGroup.eq_one_iff _).mpr a3
  have z3 : m₃ Z.val=1 := (QuotientGroup.eq_one_iff _).mpr
    (anti (by decide : 3≤4) Z.property)
  have z4 : m₄ Z.val=1 := (QuotientGroup.eq_one_iff _).mpr Z.property
  have cx : Commute (m₂ c) (m₂ x) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement m₂ c x).symm.trans u2)
  have cy : Commute (m₂ c) (m₂ y) := commutatorElement_eq_one_iff_commute.mp
    ((map_commutatorElement m₂ c y).symm.trans v2)
  have zne : M.Z≠1 := by
    rw [hz]
    intro h
    have q := (QuotientGroup.eq_one_iff _).mp h
    exact χZ ((mem_kernel_iff χ Z.property).mp q)
  have zord : orderOf M.Z=3 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    apply orderOf_eq_prime _ zne
    simpa only [show (3:ℤ)=(↑(3:ℕ):ℤ) by decide,zpow_natCast] using M.z3
  apply separates M φ₂ φ₃ φ₄
  · simpa only [hu,p₂] using u2
  · simpa only [ha,p₂] using a2
  · simpa only [hz,p₂] using z2
  · simpa only [hc,hx,p₂] using cx
  · simpa only [hc,hy,p₂] using cy
  · simpa only [hc,p₂] using ordC
  · simpa only [ha,p₃] using a3'
  · simpa only [hz,p₃] using z3
  · simpa only [hu,p₃] using ordU
  · simpa only [hz,p₄] using z4
  · simpa only [ha,p₄] using ordA
  · rw [zord]

end HaarP3TailSeparate
#print axioms HaarP3TailSeparate.separates_char
