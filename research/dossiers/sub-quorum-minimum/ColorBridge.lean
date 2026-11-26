import Majority

/- Option-valued definitions match QuorumNordhaus.lean, pinned 25711b725,
   and Ma–Sahbi–Zhang Definition 2.2. -/
namespace QuorumBounds

open SimpleGraph
variable {V C : Type} [Fintype V]

noncomputable section

def allies (G : SimpleGraph V) (f : V → Option C) (x : V) (i : C) : Finset V :=
  open Classical in Finset.univ.filter fun y => G.Adj x y ∧ f y = some i

def others (G : SimpleGraph V) (f : V → Option C) (x : V) (i : C) : Finset V :=
  open Classical in Finset.univ.filter fun y => G.Adj x y ∧ ∃ j, f y = some j ∧ j ≠ i

def IsSubQuorum (G : SimpleGraph V) (f : V → Option C) : Prop :=
  ∀ x i, f x = some i → (others G f x i).card ≤ (allies G f x i).card + 1

end
end QuorumBounds

namespace QuorumMinimum

open QuorumBounds
variable {V C : Type} [Fintype V]
noncomputable section
open Classical

def support (f : V → Option C) : Finset V := Finset.univ.filter (fun v => f v ≠ none)

theorem mem_support (f : V → Option C) (v : V) : v ∈ support f ↔ f v ≠ none := by
  simp [support]

def supportEmb (f : V → Option C) : (support f : Type) ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def supportColor (f : V → Option C) (v : support f) : Option C := f v

theorem map_supportSame (G : SimpleGraph V) (f : V → Option C)
    (x : support f) {i : C} (hx : f x = some i) :
    (localSame (G.comap (supportEmb f)) (supportColor f) x).map (supportEmb f) =
      allies G f x i := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    have h := Finset.mem_filter.mp hw
    have a := (SimpleGraph.mem_neighborFinset _ _ _).mp h.1
    simp only [allies,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨a,h.2.trans hx⟩
  · intro hy
    simp only [allies,Finset.mem_filter,Finset.mem_univ,true_and] at hy
    let w : support f := ⟨y,(mem_support f y).mpr (by rw [hy.2]; simp)⟩
    refine Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨?_,hy.2.trans hx.symm⟩,rfl⟩
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hy.1

theorem map_supportOther (G : SimpleGraph V) (f : V → Option C)
    (x : support f) {i : C} (hx : f x = some i) :
    (localOther (G.comap (supportEmb f)) (supportColor f) x).map (supportEmb f) =
      others G f x i := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    have h := Finset.mem_filter.mp hw
    have a := (SimpleGraph.mem_neighborFinset _ _ _).mp h.1
    simp only [others,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨a,?_⟩
    cases hwc : f w with
    | none => exact ((mem_support f w).mp w.property hwc).elim
    | some j =>
      refine ⟨j,hwc,fun q => h.2 ?_⟩
      exact hwc.trans (q ▸ hx.symm)
  · intro hy
    simp only [others,Finset.mem_filter,Finset.mem_univ,true_and] at hy
    obtain ⟨j,hj,hne⟩ := hy.2
    let w : support f := ⟨y,(mem_support f y).mpr (by rw [hj]; simp)⟩
    refine Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hy.1
    · intro he
      exact hne (Option.some.inj (hj.symm.trans (he.trans hx)))

theorem valid_support (G : SimpleGraph V) (f : V → Option C) (hf : IsSubQuorum G f) :
    Valid (G.comap (supportEmb f)) (supportColor f) := by
  intro x
  cases hx : f x with
  | none => exact ((mem_support f x).mp x.property hx).elim
  | some i =>
    have h := hf x i hx
    rw [←map_supportSame G f x hx,←map_supportOther G f x hx,Finset.card_map,Finset.card_map] at h
    exact h

end

#print axioms valid_support

end QuorumMinimum
