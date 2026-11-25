import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open SimpleGraph
open scoped BigOperators
namespace QuorumBounds

universe u v w
variable {V : Type u} {A : Type v} {B : Type w}
variable (f : V → Option A) (g : V → Option B)

/-- The real bipartite incidence edges; repeated corresponding vertices give one simple edge. -/
def Inc : SimpleGraph (A ⊕ B) where
  Adj a b := ∃ x : V, ∃ i : A, ∃ j : B, f x = some i ∧ g x = some j ∧
    ((a = .inl i ∧ b = .inr j) ∨ (a = .inr j ∧ b = .inl i))
  symm := by
    intro a b
    rintro ⟨x,i,j,hf,hg,h|h⟩
    · exact ⟨x,i,j,hf,hg,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨x,i,j,hf,hg,Or.inl ⟨h.2,h.1⟩⟩
  loopless := by
    intro a
    rintro ⟨x,i,j,hf,hg,h|h⟩ <;> simpa [h.1] using h.2

noncomputable def owner (x : V) : Option (Inc f g).ConnectedComponent :=
  match f x, g x with
  | some a, _ => some ((Inc f g).connectedComponentMk (.inl a))
  | none, some b => some ((Inc f g).connectedComponentMk (.inr b))
  | none, none => none

theorem owner_left {x : V} {i : A} (hi : f x = some i) :
    owner f g x = some ((Inc f g).connectedComponentMk (.inl i)) := by
  simp [owner,hi]

theorem owner_right {x : V} {j : B} (hj : g x = some j) :
    owner f g x = some ((Inc f g).connectedComponentMk (.inr j)) := by
  cases hx : f x with
  | none => simp [owner,hx,hj]
  | some i =>
    have h : (Inc f g).Adj (.inl i) (.inr j) :=
      ⟨x,i,j,hx,hj,Or.inl ⟨rfl,rfl⟩⟩
    simp [owner,hx,hj, ConnectedComponent.connectedComponentMk_eq_of_adj h]

variable [Fintype V] [Fintype A] [Fintype B]

noncomputable def members (c : (Inc f g).ConnectedComponent) : Finset V :=
  open Classical in Finset.univ.filter fun x => owner f g x = some c

omit [Fintype A] [Fintype B] in
theorem mem_members {c : (Inc f g).ConnectedComponent} {x : V} :
    x ∈ members f g c ↔ owner f g x = some c := by
  classical
  simp [members]

omit [Fintype A] [Fintype B] in
theorem members_disjoint {c d : (Inc f g).ConnectedComponent} (h : c ≠ d) :
    Disjoint (members f g c) (members f g d) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  have he := (mem_members f g).mp hx
  have he' := (mem_members f g).mp hy
  exact h (Option.some.inj (he.symm.trans he'))

noncomputable def palette (c : (Inc f g).ConnectedComponent) : Finset (A ⊕ B) :=
  open Classical in Finset.univ.filter fun a => (Inc f g).connectedComponentMk a = c

omit [Fintype V] in
theorem card_palette (c : (Inc f g).ConnectedComponent) :
    Nat.card c.supp = (palette f g c).card := by
  classical
  let e : c.supp ≃ (palette f g c) :=
    { toFun := fun a => ⟨a.val, by simpa only [palette,Finset.mem_filter,Finset.mem_univ,true_and] using a.property⟩
      invFun := fun a => ⟨a.val, by simpa only [palette,Finset.mem_filter,Finset.mem_univ,true_and] using a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr e

def Key (x : V) : Option (Sym2 (A ⊕ B)) :=
  match f x, g x with
  | some i, some j => some s(Sum.inl i, Sum.inr j)
  | _, _ => none

omit [Fintype A] [Fintype B] in
theorem exists_witness (c : (Inc f g).ConnectedComponent) (e : c.toSimpleGraph.edgeSet) :
    ∃ x : (members f g c), Key f g x.val = some (Sym2.map Subtype.val e.val) := by
  obtain ⟨⟨a,b⟩, hh⟩ := Sym2.mk_surjective e.val
  have ha : c.toSimpleGraph.Adj a b := (SimpleGraph.mem_edgeSet (G := c.toSimpleGraph)).mp (hh ▸ e.property)
  change (Inc f g).Adj a.val b.val at ha
  obtain ⟨x,i,j,hi,hj,h|h⟩ := ha
  · have ho := owner_left f g hi
    rw [← h.1] at ho
    refine ⟨⟨x,(mem_members f g).mpr (ho.trans (congrArg some a.property))⟩,?_⟩
    simp [Key,hi,hj,← hh,h.1,h.2]
  · have ho := owner_left f g hi
    rw [← h.2] at ho
    refine ⟨⟨x,(mem_members f g).mpr (ho.trans (congrArg some b.property))⟩,?_⟩
    simp [Key,hi,hj,← hh,h.1,h.2, Sym2.eq_swap]

noncomputable def witness (c : (Inc f g).ConnectedComponent) :
    c.toSimpleGraph.edgeSet → (members f g c) :=
  fun e => Classical.choose (exists_witness f g c e)

omit [Fintype A] [Fintype B] in
theorem witness_key (c : (Inc f g).ConnectedComponent) (e : c.toSimpleGraph.edgeSet) :
    Key f g (witness f g c e).val = some (Sym2.map Subtype.val e.val) :=
  Classical.choose_spec (exists_witness f g c e)

omit [Fintype V] [Fintype A] [Fintype B] in
theorem edgeEq_of_keyEq (c : (Inc f g).ConnectedComponent)
    {e e' : c.toSimpleGraph.edgeSet}
    (h : Sym2.map Subtype.val e.val = Sym2.map Subtype.val e'.val) : e = e' := by
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective h

omit [Fintype A] [Fintype B] in
theorem witness_injective (c : (Inc f g).ConnectedComponent) :
    Function.Injective (witness f g c) := by
  intro e e' he
  apply edgeEq_of_keyEq f g c
  apply Option.some.inj
  rw [← witness_key f g, ← witness_key f g, he]

theorem count_edge_le (c : (Inc f g).ConnectedComponent) :
    Nat.card c.toSimpleGraph.edgeSet ≤ (members f g c).card := by
  classical
  letI := Fintype.ofFinite c.toSimpleGraph.edgeSet
  simpa using Fintype.card_le_of_injective (witness f g c) (witness_injective f g c)

theorem palette_bound (c : (Inc f g).ConnectedComponent) :
    (palette f g c).card ≤ (members f g c).card + 1 := by
  rw [← card_palette]
  exact c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one.trans
    (Nat.add_le_add_right (count_edge_le f g c) 1)

noncomputable def Positive (c : (Inc f g).ConnectedComponent) : Prop :=
  (members f g c).card < (palette f g c).card

theorem positive_surj (c : (Inc f g).ConnectedComponent) (h : Positive f g c) :
    Function.Surjective (witness f g c) := by
  classical
  letI := Fintype.ofFinite c.toSimpleGraph.edgeSet
  have h₁ := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  change Nat.card c.supp ≤ Nat.card c.toSimpleGraph.edgeSet + 1 at h₁
  rw [card_palette f g c, Nat.card_eq_fintype_card] at h₁
  have h₂ := Fintype.card_le_of_injective (witness f g c) (witness_injective f g c)
  rw [Fintype.card_coe] at h₂
  unfold Positive at h
  refine ((Fintype.bijective_iff_injective_and_card _).mpr ⟨witness_injective f g c,?_⟩).2
  rw [Fintype.card_coe]
  omega

theorem positive_both (c : (Inc f g).ConnectedComponent) (h : Positive f g c)
    {x : V} (hx : x ∈ members f g c) : ∃ i j, f x = some i ∧ g x = some j := by
  obtain ⟨e,he⟩ := positive_surj f g c h ⟨x,hx⟩
  have hh := witness_key f g c e
  rw [he] at hh
  cases hi : f x <;> cases hj : g x <;> simp_all [Key]

omit [Fintype A] [Fintype B] in
theorem members_nonempty (hf : ∀ i, ∃ x, f x = some i)
    (hg : ∀ j, ∃ x, g x = some j) (c : (Inc f g).ConnectedComponent) :
    (members f g c).Nonempty := by
  obtain ⟨a,ha⟩ := c.nonempty_supp
  cases a with
  | inl i =>
    obtain ⟨x,hx⟩ := hf i
    exact ⟨x,(mem_members f g).mpr ((owner_left f g hx).trans (congrArg some ha))⟩
  | inr j =>
    obtain ⟨x,hx⟩ := hg j
    exact ⟨x,(mem_members f g).mpr ((owner_right f g hx).trans (congrArg some ha))⟩

end QuorumBounds
