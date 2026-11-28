import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic

open Finset
open scoped BigOperators

namespace DirectedKDSP.Rectangular
variable {I R : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [CommSemiring R]

/-- Endpoint-clipped two-factor contraction for one masked cohort row.
P includes every index strictly below w. J includes (w,e].
Backward path sums vanish. -/
theorem clipped_cohort_row (f : I → R) (X N : I → I → R) (w e : I)
    (P J : Finset I)
    (pcov : ∀ {x}, x<w → x∈P)
    (interval : ∀ {x}, w<x → x≤e → x∈J)
    (triangular : ∀ {x}, e<x → N x e=0) :
    (∑ d ∈ J.filter (w<·), (∑ c ∈ P.filter (·<w), f c * X c d) * N d e) =
      ∑ c ∈ univ.filter (·<w), f c * (∑ d ∈ univ.filter (fun d => w<d ∧ d≤e), X c d * N d e) := by
  classical
  let L := univ.filter (·<w)
  let S := J.filter (w<·)
  let T := univ.filter (fun d => w<d ∧ d≤e)
  have p : P.filter (·<w) = L := by
    ext x
    simp only [mem_filter,L,mem_univ,true_and]
    exact ⟨fun h=>h.2,fun h=>⟨pcov h,h⟩⟩
  have sub : T⊆S := by
    intro x hx
    obtain ⟨_,hw,hxe⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨interval hw hxe,hw⟩
  rw [p]
  change (∑ d ∈ S, (∑ c ∈ L, f c * X c d) * N d e) =
    ∑ c ∈ L, f c * (∑ d ∈ T, X c d * N d e)
  rw [show (∑ d ∈ S, (∑ c ∈ L, f c * X c d) * N d e) =
      ∑ d ∈ T, (∑ c ∈ L, f c * X c d) * N d e by
    symm
    apply sum_subset sub
    intro x hx hn
    have hw := (mem_filter.mp hx).2
    have ne : e<x := lt_of_not_ge (fun hh=>hn (mem_filter.mpr ⟨mem_univ _,hw,hh⟩))
    simp [triangular ne]]
  simp only [sum_mul,mul_sum,mul_assoc]
  exact sum_comm

/-- Stacking the outsider coordinate into the row is exact when the
right factor is shared. Apply the scatter mask afterward. -/
theorem shared_factor_stack {A B K C : Type*} (K0 : Finset K) (P : A → B → K → R)
    (Q : K → C → R) (allow : A → B → C → Bool) (a : A) (b : B) (c : C) :
    (if allow a b c then (∑ w ∈ K0, (fun (ab : A×B) j=>P ab.1 ab.2 j) (a,b) w * Q w c) else 0)
      = if allow a b c then (∑ w ∈ K0, P a b w * Q w c) else 0 := by rfl

#print axioms clipped_cohort_row
#print axioms shared_factor_stack
end DirectedKDSP.Rectangular
