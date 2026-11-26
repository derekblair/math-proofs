import TwoPencilChart

namespace TenPointTwoColors
abbrev P := ℤ × ℤ

def det (a b c : P) : ℤ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

def points : Fin 10 → P :=
  ![(0,17498424840),(17498424840,0),(1458202070,14582020700),(8749212420,4374606210),(504762255,16825408500),(69645472,17411368000),(5832808280,5832808280),(2692065360,13460326800),(52286130,17428710000),(6995872,17489680000)]

def A (i : Fin 2) : P := points ⟨i.val, by omega⟩
def B (i : Fin 4) : P := points ⟨i.val+2, by omega⟩
def C (i : Fin 4) : P := points ⟨i.val+6, by omega⟩

theorem distinct_points : Function.Injective points := by decide

theorem no_four (i j k l : Fin 10) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    det (points i) (points j) (points k) ≠ 0 ∨
      det (points i) (points j) (points l) ≠ 0 := by decide +revert

theorem table (i : Fin 2) (j k : Fin 4) :
    det (A i) (B j) (C k) = 0 ↔
      (i = 0 ∧ j = k) ∨ (i,j,k) = (1,0,1) ∨
      (i,j,k) = (1,1,0) ∨ (i,j,k) = (1,3,2) := by decide +revert

/-- The alternating square forces 2t=0, but then the disjoint three-edge
path forces an extra edge with the second color, a contradiction. -/
theorem no_labels {G : Type*} [AddCommGroup G] :
    ¬ ∃ f : Fin 2 → G, ∃ g h : Fin 4 → G, ∀ i j k,
      det (A i) (B j) (C k) = 0 ↔ f i+g j+h k=0 := by
  rintro ⟨f,g,h,e⟩
  have h0 : f 0+g 0+h 0=0 := (e 0 0 0).mp (by decide)
  have h1 : f 0+g 1+h 1=0 := (e 0 1 1).mp (by decide)
  have h2 : f 1+g 0+h 1=0 := (e 1 0 1).mp (by decide)
  have h3 : f 1+g 1+h 0=0 := (e 1 1 0).mp (by decide)
  have h4 : f 0+g 2+h 2=0 := (e 0 2 2).mp (by decide)
  have h5 : f 1+g 3+h 2=0 := (e 1 3 2).mp (by decide)
  have h6 : f 0+g 3+h 3=0 := (e 0 3 3).mp (by decide)
  have forced : f 1+g 2+h 3=0 := by
    calc
      f 1+g 2+h 3 =
          (f 1+g 0+h 1)+(f 1+g 1+h 0)-(f 0+g 0+h 0)-(f 0+g 1+h 1) +
          (f 0+g 2+h 2)+(f 0+g 3+h 3)-(f 1+g 3+h 2) := by abel
      _ = 0 := by rw [h0,h1,h2,h3,h4,h5,h6]; simp
  exact (by decide : det (A 1) (B 2) (C 3) ≠ 0) ((e 1 2 3).mpr forced)

end TenPointTwoColors

#print axioms TenPointTwoColors.no_four
#print axioms TenPointTwoColors.no_labels
