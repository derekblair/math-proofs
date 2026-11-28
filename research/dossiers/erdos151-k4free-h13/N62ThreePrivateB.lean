import N62PrivateLowCases

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13 Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

/-- On three unmarked owners, three B columns would require the
three support pairs to form an ambient triangle. -/
theorem b_columns_at_most_two_on_three
    (S X : Finset V)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (tf : TriangleFreeLinks G)
    (sc : S.card=12) (sf : Free (Forbidden G) (S : Set V)) (out : Disjoint X S)
    (upper : ∀ P : Finset V, Free (Forbidden G) (P : Set V) → P.card≤12)
    (triangleFree : ∀ a∈S, ∀ b∈S, ∀ c∈S, G a b → G a c → G b c → False)
    (u3 : (S\(nearFrame G S X sym irr tf sc sf out upper).marks).card=3) :
    bcnt G S X≤2 := by
  classical
  let F := nearFrame G S X sym irr tf sc sf out upper
  let U := S\F.marks
  obtain ⟨a,b,c,ab,ac,bc,eq⟩ := card_eq_three.mp u3
  change U={a,b,c} at eq
  have su (x : V) (hx : x∈({a,b,c}:Finset V)) : x∈S := by
    rw [←eq] at hx
    exact (mem_sdiff.mp hx).1
  have missing : ∃ p q r : V, U={p,q,r} ∧ ¬G p q ∧ r∈S := by
    by_cases ea : G a b
    · by_cases eb : G a c
      · have ec : ¬G b c := triangleFree a (su _ (by simp)) b (su _ (by simp)) c (su _ (by simp)) ea eb
        exact ⟨b,c,a,by rw [eq]; ext x; simp only [mem_insert,mem_singleton]; tauto,ec,su _ (by simp)⟩
      · exact ⟨a,c,b,by rw [eq]; ext x; simp only [mem_insert,mem_singleton]; tauto,eb,su _ (by simp)⟩
    · exact ⟨a,b,c,eq,ea,su _ (by simp)⟩
  obtain ⟨p,q,r,e,pq,rs⟩ := missing
  let B := weightedSet X (Bcol G S)
  have sub : B⊆privateFirst G S X r := by
    intro x hx
    obtain ⟨xx,xb⟩ := mem_filter.mp hx
    have blocked := all_exterior_blocked_12 G S sc upper x (Finset.disjoint_left.mp out xx)
    obtain ⟨i,is,j,js,ij,edge,_,_,sup⟩ := Bcol_adjacent_support G S x sym irr sf blocked xb
    have iU : i∈U := mem_sdiff.mpr ⟨is,B_support_unmarked G S X sym irr tf sc sf out upper xx xb (by simp [sup])⟩
    have jU : j∈U := mem_sdiff.mpr ⟨js,B_support_unmarked G S X sym irr tf sc sf out upper xx xb (by simp [sup])⟩
    rw [e] at iU jU
    simp only [mem_insert,mem_singleton] at iU jU
    have rr : r=i ∨ r=j := by
      rcases iU with rfl|rfl|rfl <;> rcases jU with rfl|rfl|rfl
      all_goals first | exact False.elim (ij rfl) | exact False.elim (pq edge) |
        exact False.elim (pq (sym edge)) | exact Or.inl rfl | exact Or.inr rfl
    have supp : r∈support G S x := by simpa [sup] using rr
    exact mem_filter.mpr ⟨xx,Or.inl ⟨Or.inr xb,(mem_ns (G:=G) S x).mpr (mem_filter.mp supp)⟩⟩
  have cc := card_le_card sub
  have cap := private_slots_charged G S X sym irr tf sc sf out upper r rs
  change B.card≤2
  omega

#print axioms b_columns_at_most_two_on_three
end Erdos151N62
