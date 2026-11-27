import Exact11
import AnchorBlocks15
import Eliminate15TreeCert16
import Eliminate15AllRows
import FastPaintCover15

namespace IU.IU15Tree

open IU.Eliminate

theorem prefix_cap15 (F : Finset Nat)
    (v : ∀ a∈F, a∈admissible 15 2 2)
    (edgeF : ∀ a∈F, ∀ b∈F, a≠b → edge 15 2 2 a b=true) :
    F.card≤4092 := by
  apply clique_cap_of_elimination (n:=15) (p:=2) (q:=2) (m:=4092) (r:=4) colors phase F
  · intro i
    exact root.at_good rootGood i.val
  · intro a ha
    have E := paint_cover (v a ha)
    have equality : root.mask=rootMaskLit := rootMaskEq
    rw [←equality] at E
    obtain ⟨i,hi,h⟩ := root.mask_cover rootValid E
    exact ⟨⟨i,hi⟩,h⟩
  · exact edgeF
  · intro a ha small
    obtain ⟨ab,hV⟩ := List.mem_filter.mp (v a ha)
    have w := of_decide_eq_true ((Bool.and_eq_true_iff.mp hV).1)
    have small' : stage a<2 := by unfold phase at small; split at small <;> omega
    exact structured_rows allRows pivotFacts w.1 w.2 small'
  · refine ⟨IU15Anchor.anchorFamily,by rw [IU15Anchor.anchor_size],?_⟩
    intro a ha high
    have n : a<32768 := List.mem_range.mp (List.mem_filter.mp (v a ha)).1
    have G : ¬Outer a := by
      intro O
      have small : stage a < 2 := by
        by_cases h : Init a <;> simp [stage,h,O]
      unfold phase at high
      split at high <;> omega
    unfold Outer at G
    exact IU15Anchor.into_anchor n (by omega) (by omega)

theorem upper15 (F : Sys) (ok : IsIU F 15 2 2) : F.card≤4092 :=
  cap_of_prefix ok prefix_cap15

theorem upper14 (F : Sys) (ok : IsIU F 14 2 2) : F.card≤2046 :=
  upper_with_free (by decide) F ok upper15

theorem exact14 : Exact 14 2046 :=
  ⟨upper14, attained (l:=6) (r:=8) (by decide) (by decide) (by decide) IU15Anchor.product_len14⟩

theorem exact15 : Exact 15 4092 :=
  ⟨upper15, attained (l:=6) (r:=8) (by decide) (by decide) (by decide) IU15Anchor.product_len15⟩

#print axioms exact14
#print axioms exact15
end IU.IU15Tree
