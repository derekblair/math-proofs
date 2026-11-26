import HaarClassFourFinite
import HaarAnyPorts
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card

namespace HaarMetaAlgebraCore
open scoped commutatorElement
open HaarClass4Generate HaarAllNoncommuting
universe u v w
variable {G : Type u} {Q : Type v} {R : Type w} [Group G] [Group Q] [Group R]

def Meta (G : Type*) [Group G] : Prop :=
  ∀ a b : commutator G, a*b=b*a

theorem map_comm_le (f : G→*Q) : (commutator G).map f ≤ commutator Q := by
  rw [map_commutator_eq,commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem subgroup_meta (S : Subgroup G) (h : Meta G) : Meta S := by
  intro a b
  let A : commutator G := ⟨a.val.val,map_comm_le S.subtype (Subgroup.mem_map_of_mem S.subtype a.property)⟩
  let B : commutator G := ⟨b.val.val,map_comm_le S.subtype (Subgroup.mem_map_of_mem S.subtype b.property)⟩
  apply Subtype.ext
  apply Subtype.ext
  change a.val.val*b.val.val=b.val.val*a.val.val
  exact congrArg (fun z : commutator G => z.val) (h A B)

theorem ab_map_surj : Function.Surjective (Abelianization.of : G→*Abelianization G) :=
  QuotientGroup.mk'_surjective (commutator G)

theorem ab_map_normal (h : Meta G) :
    ∀ a b : (Abelianization.of : G→*Abelianization G).ker, a*b=b*a := by
  change ∀ a b : ((Abelianization.of : G→*Abelianization G).ker), _
  rw [Abelianization.ker_of]
  exact h

theorem odd_of_surj (f : G→*Q) (onto : Function.Surjective f) (odd : Odd (Nat.card G)) :
    Odd (Nat.card Q) := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f onto).toEquiv]
  exact Odd.of_dvd_nat odd f.ker.card_quotient_dvd_card

theorem no_two_fin_odd {A : Type*} [AddCommGroup A] [Finite A] (hodd : Odd (Nat.card A))
    (a : A) (h : a+a=0) : a=0 := by
  have h2 : addOrderOf a ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by simpa [two_nsmul] using h)
  have hA : addOrderOf a ∣ Nat.card A := addOrderOf_dvd_natCard a
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h2 with o | o
  · simpa using o
  · exact False.elim (by
      have e : 2∣Nat.card A := by simpa only [o] using hA
      rcases hodd with ⟨k,hk⟩
      rcases e with ⟨j,hj⟩
      omega)

theorem span_after (f : G→*Q) (onto : Function.Surjective f) (x y : G) (gen : Generates x y) :
    AddSubgroup.closure ({Additive.ofMul (f x),Additive.ofMul (f y)} : Set (Additive Q))=⊤ := by
  have g := HaarClass4Generate.map_gen f onto gen
  have gg : Subgroup.closure ({f x,f y}:Set Q)=⊤ := g
  have tr := congrArg Subgroup.toAddSubgroup gg
  rw [Subgroup.toAddSubgroup_closure] at tr
  have ee : Additive.toMul ⁻¹' ({f x,f y}:Set Q) =
      ({Additive.ofMul (f x),Additive.ofMul (f y)}:Set (Additive Q)) := by
    ext z
    rfl
  rw [ee] at tr
  exact tr

theorem ab_kernel_comp (f : G→*Q) (e : Q→*R) (inj : Function.Injective e)
    (ab : ∀ a b : f.ker, a*b=b*a) :
    ∀ a b : (e.comp f).ker, a*b=b*a := by
  rw [MonoidHom.ker_comp_of_injective f e inj]
  exact ab

theorem extend_from_generated (x y : G) (odd : Odd (Nat.card G)) (met : Meta G)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (solve : ∀ (S : Type u) [Group S] [Finite S] (X Y : S), Odd (Nat.card S) → Meta S →
             Generates X Y → X≠1 → Y≠1 → X≠Y → ∃ n, n∈[4,8,16,32] ∧ HasCycle X Y n)
    [Finite G] :
    ∃ n, n∈[4,8,16,32] ∧ HasCycle x y n := by
  let S := Subgroup.closure ({x,y} : Set G)
  let X : S := ⟨x,Subgroup.subset_closure (by simp)⟩
  let Y : S := ⟨y,Subgroup.subset_closure (by simp)⟩
  have gen : Generates X Y := by
    apply Subgroup.map_subtype_inj.mp
    rw [MonoidHom.map_closure,Set.image_pair,Subgroup.map_top,Subgroup.subtype_range]
    rfl
  obtain ⟨n,hn,w⟩ := solve (↥S) X Y (Odd.of_dvd_nat odd S.card_subgroup_dvd_card)
    (subgroup_meta S met) gen (fun z => hx (congrArg (fun t : ↥S => t.val) z))
    (fun z => hy (congrArg (fun t : ↥S => t.val) z)) (fun z => hxy (congrArg (fun t : ↥S => t.val) z))
  exact ⟨n,hn,HaarClassFourFinite.mapped_cycle S.subtype Subtype.val_injective X Y w⟩

end HaarMetaAlgebraCore
#print axioms HaarMetaAlgebraCore.extend_from_generated
