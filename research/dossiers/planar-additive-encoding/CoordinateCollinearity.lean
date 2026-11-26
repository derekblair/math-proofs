import Mathlib.Tactic

namespace CoordinateCollinearity

abbrev Pt := ℤ × ℤ

def det (a b c : Pt) : ℤ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

def A (i : Bool) : Pt := if i then (0,1) else (1,0)
def B (i : Bool) : Pt := if i then (3,0) else (0,0)
def C (i : Bool) : Pt := if i then (0,2) else (2,0)

/-- An identification gadget: three distinct planar points are collinear
exactly when the two first-vector bits are identical and the two source bits
are not both set. -/
theorem gadget (i j k : Bool) : det (A i) (B j) (C k) = 0 ↔
    i = k ∧ ¬ (i = true ∧ j = true) := by decide +revert

theorem distinct_gadget (i j k : Bool) :
    A i ≠ B j ∧ A i ≠ C k ∧ B j ≠ C k := by decide +revert

variable {I : Type*}

/-- Every coordinate of three lists may choose its own geometric line. -/
def EveryCoordinate (a b c : I → Pt) : Prop :=
  ∀ i, det (a i) (b i) (c i) = 0

def Orthogonal (x y : I → Bool) : Prop :=
  ∀ i, ¬ (x i = true ∧ y i = true)

/-- Exact existential transfer from OV, with the first bit-vector list used
in positions A and C. Each tuple position is simply mapped coordinatewise. -/
theorem coordinate_reduction (X Y : Set (I → Bool)) :
    (∃ x ∈ X, ∃ y ∈ Y, Orthogonal x y) ↔
      ∃ a ∈ ((fun x => A ∘ x) '' X), ∃ b ∈ ((fun y => B ∘ y) '' Y),
        ∃ c ∈ ((fun x => C ∘ x) '' X), EveryCoordinate a b c := by
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    exact ⟨A ∘ x,⟨x,hx,rfl⟩,B ∘ y,⟨y,hy,rfl⟩,C ∘ x,⟨x,hx,rfl⟩,
      fun i => (gadget (x i) (y i) (x i)).mpr ⟨rfl,h i⟩⟩
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,_,⟨w,hw,rfl⟩,hc⟩
    have eql : x = w := by
      funext i
      exact ((gadget (x i) (y i) (w i)).mp (hc i)).1
    subst w
    exact ⟨x,hx,y,hy,fun i => ((gadget (x i) (y i) (x i)).mp (hc i)).2⟩

/-- Pairwise coordinate collinearity need not imply collinearity of the
concatenated points: a line in the product must use one common parameter. -/
theorem no_common_parameter :
    (∀ i j : Bool, det (A false) (B j) (C i) = 0 ↔ i=false) ∧
    ¬ ∃ t : ℚ, (0 : ℚ) = 1+t*(2-1) ∧ (3 : ℚ) = 1+t*(2-1) := by
  constructor
  · decide
  · rintro ⟨t,h0,h3⟩
    linarith

end CoordinateCollinearity

#print axioms CoordinateCollinearity.coordinate_reduction
#print axioms CoordinateCollinearity.no_common_parameter
