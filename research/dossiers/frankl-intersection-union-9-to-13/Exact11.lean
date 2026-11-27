import Exact9
import PackedColor11
import FreeSite
import ProductWitness

namespace IU

theorem cap_of_prefix {F : Sys} {n k : Nat} (ok : IsIU F n 2 2)
    (bound : ∀ G : Finset Nat, (∀ a∈G, a∈admissible n 2 2) →
      (∀ a∈G, ∀ b∈G, a≠b → edge n 2 2 a b=true) → G.card≤k) :
    F.card≤k := by
  obtain ⟨H,e,V,s⟩ := stabilize F ok
  have C := prefix_closed_of_elementary H V.1 s
  obtain ⟨c,U,E⟩ := image_in_prefix_graph (by decide : 0<(2:Nat)) V C
  exact (c.trans e) ▸ bound _ U E

theorem upper11 (F : Sys) (ok : IsIU F 11 2 2) : F.card≤220 :=
  cap_of_prefix ok prefix_cap11
theorem upper_with_free {n k : Nat} (hn : 2≤n) (F : Sys) (ok : IsIU F n 2 2)
    (cap : ∀ X : Sys, IsIU X (n+1) 2 2 → X.card≤2*k) :
    F.card≤k := by
  obtain ⟨D,c⟩ := lift_double F ok hn
  have L := cap (double F n) D
  rw [c] at L
  omega

theorem upper10 (F : Sys) (ok : IsIU F 10 2 2) : F.card≤110 :=
  upper_with_free (by decide) F ok upper11
abbrev Exact (n k : Nat) : Prop :=
  (∀ F : Sys, IsIU F n 2 2 → F.card≤k) ∧ (∃ F : Sys, IsIU F n 2 2 ∧ F.card=k)

theorem attained {n l r k : Nat}
    (L : l≤n) (R : r≤n) (Q : 2≤r)
    (E : (productMasks n l r 2 2).length=k) :
    ∃ F : Sys, IsIU F n 2 2 ∧ F.card=k := E ▸ product_family n l r 2 2 L R Q

set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem exact10 : Exact 10 110 :=
  ⟨upper10, attained (l:=4) (r:=6) (by decide) (by decide) (by decide) (by decide +kernel)⟩
theorem exact11 : Exact 11 220 :=
  ⟨upper11, attained (l:=4) (r:=6) (by decide) (by decide) (by decide) (by decide +kernel)⟩
#print axioms exact10
#print axioms exact11
end IU
