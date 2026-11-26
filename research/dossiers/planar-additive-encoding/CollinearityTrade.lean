import Mathlib.Tactic

namespace CollinearityTrade

abbrev P := ℤ × ℤ

def det (a b c : P) : ℤ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

def points : Fin 9 → P :=
  ![(-3,0),(1,-1),(-2,-3),(3,-3),(2,1),(2,-1),(-1,-1),(0,-3),(0,-2)]

def a (i : Fin 3) : P := points ⟨i.val, by omega⟩
def b (i : Fin 3) : P := points ⟨i.val+3, by omega⟩
def c (i : Fin 3) : P := points ⟨i.val+6, by omega⟩

theorem distinct_points : Function.Injective points := by decide
theorem five_hits :
    det (a 0) (b 0) (c 0) = 0 ∧ det (a 1) (b 1) (c 1) = 0 ∧
    det (a 2) (b 2) (c 2) = 0 ∧ det (a 1) (b 2) (c 0) = 0 ∧
    det (a 2) (b 0) (c 1) = 0 := by decide
theorem missed : det (a 0) (b 1) (c 2) ≠ 0 := by decide

theorem exact_hits (i j k : Fin 3) :
    det (a i) (b j) (c k) = 0 ↔
      (i,j,k) = (0,0,0) ∨ (i,j,k) = (1,1,1) ∨ (i,j,k) = (2,2,2) ∨
      (i,j,k) = (1,2,0) ∨ (i,j,k) = (2,0,1) := by decide +revert

/-- Even ignoring colors, there are no additional collinear triples. -/
theorem all_uncolored_hits (i j k : Fin 9) (hij : i < j) (hjk : j < k) :
    det (points i) (points j) (points k) = 0 ↔
      (i,j,k) = (0,3,6) ∨ (i,j,k) = (1,4,7) ∨ (i,j,k) = (2,5,8) ∨
      (i,j,k) = (1,5,6) ∨ (i,j,k) = (2,3,7) := by
  decide +revert

/-- The two multisets of triples have identical one-coordinate marginals. -/
theorem additive_closure {G : Type*} [AddCommGroup G] (f g h : Fin 3 → G)
    (e0 : f 0 + g 0 + h 0 = 0) (e1 : f 1 + g 1 + h 1 = 0)
    (e2 : f 2 + g 2 + h 2 = 0) (e3 : f 1 + g 2 + h 0 = 0)
    (e4 : f 2 + g 0 + h 1 = 0) : f 0 + g 1 + h 2 = 0 := by
  have e :
      (f 0 + g 1 + h 2) + (f 1 + g 2 + h 0) + (f 2 + g 0 + h 1) =
        (f 0 + g 0 + h 0) + (f 1 + g 1 + h 1) + (f 2 + g 2 + h 2) := by abel
  simpa only [e0,e1,e2,e3,e4,add_zero] using e

/-- A single choice of three per-point additive labels cannot exactly encode
the collinearity relation on this instance in any additive abelian group. -/
theorem no_pointwise_linearization {G : Type*} [AddCommGroup G] :
    ¬ ∃ f g h : Fin 3 → G, ∀ i j k,
      det (a i) (b j) (c k) = 0 ↔ f i + g j + h k = 0 := by
  rintro ⟨f,g,h,e⟩
  obtain ⟨h0,h1,h2,h3,h4⟩ := five_hits
  exact missed ((e 0 1 2).mpr (additive_closure f g h
    ((e 0 0 0).mp h0) ((e 1 1 1).mp h1) ((e 2 2 2).mp h2)
    ((e 1 2 0).mp h3) ((e 2 0 1).mp h4)))

end CollinearityTrade

#print axioms CollinearityTrade.no_pointwise_linearization
