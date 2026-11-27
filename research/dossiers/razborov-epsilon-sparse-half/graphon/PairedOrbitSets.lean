import PairOrient
open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
universe u

/-- Orient fixed-point-free valid profile orbits and take their disjoint measurable
fibers inside S. The empty dummy pair makes the index inhabited. -/
theorem orbit_pair_sets {X : Type*} {Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (S : Set X) (ms : MeasurableSet S)
    (p : X → Y) (pm : Measurable p) (flip : Y → Y) (inv : Involutive flip)
    (A : Set Y) (ac : A.Countable) (closed : ∀ y∈A, flip y∈A)
    (free : ∀ y∈A, flip y≠y) :
    ∃ (I : Type u) (_ : Countable I) (_ : Nonempty I) (P Q : I → Set X),
    (∀ i, MeasurableSet (P i)) ∧ (∀ i, MeasurableSet (Q i)) ∧
    (∀ i, P i ∪ Q i ⊆ S) ∧ (∀ i, Disjoint (P i) (Q i)) ∧
    Pairwise (Disjoint on fun i => P i ∪ Q i) ∧
    (∀ i, (P i=∅ ∧ Q i=∅) ∨ ∃ a∈A, P i=S∩p⁻¹'{a} ∧ Q i=S∩p⁻¹'{flip a}) ∧
    ∀ x∈S, ∀ y∈S, p x∈A → p y=flip (p x) →
      ∃ i, (x∈P i ∧ y∈Q i) ∨ (x∈Q i ∧ y∈P i) := by
  letI : Countable A := ac.to_subtype
  let f (a : A) : A := ⟨flip a.val,closed _ a.property⟩
  have finv : Involutive f := fun a => Subtype.ext (inv a.val)
  have fne (a : A) : f a≠a := fun h => free _ a.property (congrArg Subtype.val h)
  obtain ⟨R,orient,cover,rc⟩ := orient_countable_involution f finv fne
  let C (a : A) := S∩p⁻¹'{a.val}
  have cm (a : A) : MeasurableSet (C a) := ms.inter (pm (measurableSet_singleton _))
  have dis (a b : A) (hne : a≠b) : Disjoint (C a) (C b) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : p x=a.val := hx.2
    have hy' : p x=b.val := hy.2
    exact hne (Subtype.ext (hx'.symm.trans hy'))
  let P : Option ↥R → Set X := fun i => i.elim ∅ (fun a=>C a.val)
  let Q : Option ↥R → Set X := fun i => i.elim ∅ (fun a=>C (f a.val))
  letI : Countable R := rc.to_subtype
  refine ⟨Option ↥R,inferInstance,inferInstance,P,Q,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; cases i with
    | none => exact MeasurableSet.empty
    | some a => exact cm _
  · intro i; cases i with
    | none => exact MeasurableSet.empty
    | some a => exact cm _
  · intro i; cases i with
    | none => simp [P,Q]
    | some a => exact union_subset inter_subset_left inter_subset_left
  · intro i; cases i with
    | none => simp [P,Q]
    | some a => exact dis _ _ (Ne.symm (fne a.val))
  · intro i j ne
    cases i with
    | none => simp [P,Q]
    | some a =>
      cases j with
      | none => simp [P,Q]
      | some b =>
        have ab : a.val≠b.val := fun h=>ne (congrArg some (Subtype.ext h))
        have afb : a.val≠f b.val := fun h=>(orient b.val).mp b.property (h ▸ a.property)
        have fab : f a.val≠b.val := fun h=>(orient a.val).mp a.property (h.symm ▸ b.property)
        have fafb : f a.val≠f b.val := fun h=>ab (finv.injective h)
        change Disjoint (C a.val∪C (f a.val)) (C b.val∪C (f b.val))
        exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨dis _ _ ab,dis _ _ afb⟩,
          disjoint_union_right.mpr ⟨dis _ _ fab,dis _ _ fafb⟩⟩
  · intro i; cases i with
    | none => exact Or.inl ⟨rfl,rfl⟩
    | some a => exact Or.inr ⟨a.val.val,a.val.property,rfl,rfl⟩
  · intro x xs y ys px py
    let a : A := ⟨p x,px⟩
    rcases cover a with h|h
    · exact ⟨some ⟨a,h⟩,Or.inl ⟨⟨xs,rfl⟩,⟨ys,py⟩⟩⟩
    · refine ⟨some ⟨f a,h⟩,Or.inr ⟨⟨xs,?_⟩,⟨ys,py⟩⟩⟩
      change p x=(f (f a)).val
      rw [finv]

#print axioms orbit_pair_sets
end SparseHalfGraphon
