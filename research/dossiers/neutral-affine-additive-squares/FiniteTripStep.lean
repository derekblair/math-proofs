import FiniteTrip

namespace FiniteTripStep
open FiniteTrip TripTrace CutLift CutOrder AffineAddress
variable (D : Finset ℤ) (f : ℤ → List ℤ)
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)

include closed in
theorem child_mem {w : List ℤ} (h : ∀ z ∈ w, z∈D) :
    ∀ z ∈ w.flatMap f, z ∈ D := by
  intro z hz
  obtain ⟨x,hx,hy⟩ := List.mem_flatMap.mp hz
  exact closed x (h x hx) z hy

def indices {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D) (a : Offset f T) :
    Choices D f (restrictShape D T h) :=
  (idxFin a.a,idxFin a.b,idxFin a.c)

def offsets {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D)
    (p : Choices D f (restrictShape D T h)) : Offset f T :=
  ⟨cA p,cB p,cC p⟩

theorem roundTrip {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D) (a : Offset f T) :
    offsets D f T h (indices D f T h a)=a := by
  cases a with
  | mk aa bb cc =>
    change Offset.mk (byIndex _ (idxFin aa)) (byIndex _ (idxFin bb)) (byIndex _ (idxFin cc))
      = Offset.mk aa bb cc
    simp only [byIndex_round]

theorem step_matches {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D)
    (o : ordered T) (i : Edge D f) (he : src D f i = restrictShape D T h) :
    ∃ p : Offset f T, ordered (desc f T p) ∧
      dst D f closed i = restrictShape D (desc f T p) (child_mem D f closed h) ∧
      stamp D f i = σ p.a.head + σ p.c.head - (σ p.b.head + σ p.b.head) := by
  rcases i with ⟨⟨S,j⟩,hj⟩
  change S = restrictShape D T h at he
  subst S
  let p := offsets D f T h j
  have hh := shape_step f T p o
  refine ⟨p,hh.1.mpr hj,?_ ,rfl⟩
  apply erase_inj
  rw [erase_shape,hh.2]
  rfl

theorem step_exists {w : List ℤ} (T : Triple w) (h : ∀ z ∈ w, z∈D)
    (o : ordered T) (p : Offset f T) (op : ordered (desc f T p)) :
    ∃ i : Edge D f, src D f i = restrictShape D T h ∧
      dst D f closed i = restrictShape D (desc f T p) (child_mem D f closed h) ∧
      stamp D f i = σ p.a.head + σ p.c.head - (σ p.b.head + σ p.b.head) := by
  let j := indices D f T h p
  have r : offsets D f T h j=p := roundTrip D f T h p
  have hg : guardState D f (restrictShape D T h) j := by
    change CutOrder.guard f (shape T) (offsets D f T h j).a
      (offsets D f T h j).b (offsets D f T h j).c
    rw [r]
    exact (shape_step f T p o).1.mp op
  let i : Edge D f := ⟨⟨restrictShape D T h,j⟩,hg⟩
  refine ⟨i,rfl,?_,?_⟩
  · apply erase_inj
    rw [erase_shape,(shape_step f T p o).2]
    change update f (shape T) (offsets D f T h j).a (offsets D f T h j).b
      (offsets D f T h j).c = _
    rw [r]
  · change σ (offsets D f T h j).a.head + σ (offsets D f T h j).c.head -
      (σ (offsets D f T h j).b.head + σ (offsets D f T h j).b.head) = _
    rw [r]

end FiniteTripStep

#print axioms FiniteTripStep.step_matches
#print axioms FiniteTripStep.step_exists
