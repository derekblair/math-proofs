import RibbonMetaClose
import HaarClass4Generate

namespace RibbonMeta
open HaarClass4Structure HaarClass4Generate HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]

theorem lower_drop {k n : ℕ} (nil : LS G n=⊥) (start : LS G k=LS G (k+1)) :
    LS G k=⊥ := by
  by_cases h : n≤k
  · exact eq_bot_iff.mpr ((Subgroup.lowerCentralSeries_antitone ⊤ h).trans nil.le)
  · have later (i : ℕ) : LS G (k+i)=LS G (k+i+1) := by
      induction i with
      | zero => exact start
      | succ i ih =>
        exact congrArg (fun T : Subgroup G => ⁅T,(⊤ : Subgroup G)⁆) ih
    have flat (i : ℕ) : LS G k=LS G (k+i) := by
      induction i with
      | zero => rfl
      | succ i ih => exact ih.trans (later i)
    obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le (by omega : k≤n)
    exact (flat i).trans (hi ▸ nil)

theorem comm_if_projected_trivial {n : ℕ} (nil : LS G n=⊥) (x y : G)
    (gen : Generates x y) (hc : portC x y∈LS G 2) : portC x y=1 := by
  let S := LS G 2
  let φ := QuotientGroup.mk' S
  have g := map_gen φ (QuotientGroup.mk'_surjective S) gen
  have r : Commute (φ x) (φ y) := by
    have C : φ (portC x y)=1 := (QuotientGroup.eq_one_iff _).mpr hc
    change φ x*φ y=φ y*φ x
    simpa only [map_mul,C,mul_one] using congrArg φ (ports_xy x y)
  let : IsMulCommutative (G ⧸ S) := gen_comm _ _ g r
  have zero : LS (G ⧸ S) 1=⊥ :=
    Subgroup.top_lowerCentralSeries_one.trans (commutator_eq_bot (G ⧸ S))
  have h := map_ls φ (QuotientGroup.mk'_surjective S) 1
  rw [zero,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at h
  have d : LS G 1=LS G 2 :=
    le_antisymm h ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup G)) (by decide : 1≤2))
  have hC := layer_c x y
  rw [lower_drop nil d,Subgroup.mem_bot] at hC
  exact hC

theorem subgroup_meta (m : Meta G) (S : Subgroup G) : Meta S := by
  intro a ha b hb
  have incl : (LS S 1).map S.subtype ≤ LS G 1 := by
    rw [Subgroup.top_subtype_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono 1 (show S≤⊤ from le_top)
  have h := m a.val (incl (Subgroup.mem_map_of_mem _ ha)) b.val
    (incl (Subgroup.mem_map_of_mem _ hb))
  exact Subtype.ext h.eq

end RibbonMeta
#print axioms RibbonMeta.lower_drop
#print axioms RibbonMeta.subgroup_meta
