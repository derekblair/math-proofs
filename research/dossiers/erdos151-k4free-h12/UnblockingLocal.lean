import UnblockingGraph

namespace Erdős151
variable {V : Type*} {G : V → V → Prop} {S : Set V} {x u : V}

def Support (G : V → V → Prop) (S : Set V) (x : V) : Set V :=
  {v | v ∈ S ∧ G x v}

theorem blocked_witness
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ a, ¬ G a a) (hS : Free (Forbidden G) S)
    (hb : ¬ Free (Forbidden G) (insert x S)) :
    (∃ a ∈ Support G S x, Lone G x a) ∨
    (∃ a ∈ Support G S x, ∃ b ∈ Support G S x, a ≠ b ∧ G a b)
    := by
  classical
  unfold Free at hb
  push Not at hb
  obtain ⟨A,hA,hsub⟩ := hb
  have hm : x ∈ A := by
    by_contra he
    apply hS A hA
    intro y hy
    exact (Set.mem_insert_iff.mp (hsub hy)).resolve_left (fun e => he (e ▸ hy))
  have symL {a b} (h : Lone G a b) : Lone G b a :=
    ⟨sym h.1, fun y hy => h.2 y hy.symm⟩
  have ret {a b} (h : Lone G a b) (hxs : a = x)
      (hbs : b ∈ insert x S) : (∃ a ∈ Support G S x, Lone G x a) := by
    subst a
    by_cases hbx : b = x
    · subst b
      exact False.elim (h.2 x ⟨h.1,h.1⟩)
    · exact ⟨b,⟨(Set.mem_insert_iff.mp hbs).resolve_left hbx,h.1⟩,h⟩
  rcases hA with ⟨a,b,rfl,hl⟩ | ⟨a,b,c,rfl,hab,hbc,hac⟩
  · left
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with e|e
    · exact ret hl e.symm (hsub (by simp))
    · exact ret (symL hl) e.symm (hsub (by simp))
  · right
    have neq {i j} (h : G i j) : i ≠ j := by
      intro e
      subst j
      exact loopless i h
    have fa := hsub (show a ∈ ({a,b,c} : Set V) by simp)
    have fb := hsub (show b ∈ ({a,b,c} : Set V) by simp)
    have fc := hsub (show c ∈ ({a,b,c} : Set V) by simp)
    have lift {i} (hi : i ∈ insert x S) (ha : G x i) : i ∈ Support G S x :=
      ⟨(Set.mem_insert_iff.mp hi).resolve_left (neq (sym ha)), ha⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with e|e|e
    · subst a
      exact ⟨b,lift fb hab,c,lift fc hac,neq hbc,hbc⟩
    · subst b
      exact ⟨a,lift fa (sym hab),c,lift fc hbc,neq hac,hac⟩
    · subst c
      exact ⟨a,lift fa (sym hac),b,lift fb (sym hbc),neq hab,hab⟩

theorem extend_of_clean_support
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ a, ¬ G a a)
    (hS : Free (Forbidden G) S)
    (noLone : ∀ a ∈ Support G S x, ¬ Lone G x a)
    (indep : ∀ a ∈ Support G S x, ∀ b ∈ Support G S x, ¬ G a b) :
    Free (Forbidden G) (insert x S) := by
  classical
  by_contra hb
  rcases blocked_witness (G := G) (S := S) (x := x) sym loopless hS hb with ⟨a,ha,hl⟩ | ⟨a,ha,b,hb,_,hab⟩
  · exact noLone a ha hl
  · exact indep a ha b hb hab

theorem private_of_residual_support
    (sym : ∀ {a b}, G a b → G b a) (loopless : ∀ a, ¬ G a a)
    (hS : Free (Forbidden G) S)
    (noLone : ∀ a ∈ Support G S x, a ≠ u → ¬ Lone G x a)
    (one : ∀ a ∈ Support G S x, ∀ b ∈ Support G S x, a ≠ u → b ≠ u → a = b) :
    Free (Forbidden G) (insert x (S \ {u})) := by
  apply extend_of_clean_support (G := G) sym loopless
  · intro A hA hsub
    exact hS A hA (fun v hv => (hsub hv).1)
  · intro a ha
    exact noLone a ⟨ha.1.1,ha.2⟩ (by simpa using ha.1.2)
  · intro a ha b hb
    have e := one a ⟨ha.1.1,ha.2⟩ b ⟨hb.1.1,hb.2⟩
      (by simpa using ha.1.2) (by simpa using hb.1.2)
    subst b
    exact loopless a

theorem private_lone_isolated
    (sym : ∀ {a b}, G a b → G b a)
    (hl : Lone G x u) (hy : G y u) : ¬ G x y :=
  fun h => hl.2 y ⟨h,sym hy⟩

#print axioms extend_of_clean_support
#print axioms private_of_residual_support
#print axioms private_lone_isolated
#print axioms blocked_witness
end Erdős151
