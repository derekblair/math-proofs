import Ribbon6Family
import Ribbon6Invert
import Ribbon6P3Chart
namespace Ribbon6
open HaarClass4Structure Ribbon5Bridge
variable {G : Type*} [Group G]

private theorem prepend32 (x y : G) (i : Nat) (h : i≤32) :
    pathAt x y wa i = pathAt x y wc i := by
  have E : wa.toList = wc.toList.take 32 := by decide +kernel
  simp only [pathAt,E,List.take_take,Nat.min_eq_left h]

/-- A transport of actual equality into any covered character table suffices.
There is no assumption that the finite quotient character detects all equality. -/
theorem cycle_of_good_table (nil : LS G 6=⊥) (x y : G) (q t : Fin 3) (h : OK q t)
    (key : ∀ i j : Fin 64, pathAt x y wc i.val = pathAt x y wc j.val →
      pkey q t i = pkey q t j) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  by_cases z : residue x y=1
  · left
    apply cycle_from_at x y wa (by decide) (by rw [a_end,z]; rfl)
    intro i j l E
    let I : Fin 64 := ⟨i.val,by omega⟩
    let J : Fin 64 := ⟨j.val,by omega⟩
    have ei : pathAt x y wa i.val = pathAt x y wc I.val := prepend32 x y _ i.isLt.le
    have ej : pathAt x y wa j.val = pathAt x y wc J.val := prepend32 x y _ j.isLt.le
    have m := p3chart q t h I J l (key I J (ei.symm.trans (E.trans ej)))
    change same i.val j.val at m
    unfold same at m
    omega
  · right
    apply cycle_from_at x y wc (by decide) (close nil x y)
    intro i j l E
    exact mate_sep x y z _ _ (p3chart q t h i j l (key i j E)) E

theorem cycle_of_tables (nil : LS G 6=⊥) (x y : G) (q t : Fin 3)
    (keyA : ∀ i j : Fin 64, pathAt x y wc i.val = pathAt x y wc j.val →
      pkey q t i = pkey q t j)
    (keyB : ∀ i j : Fin 64, pathAt x⁻¹ y wc i.val = pathAt x⁻¹ y wc j.val →
      pkey (-q) (-t) i = pkey (-q) (-t) j) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  rcases p3case q t with g|g
  · exact cycle_of_good_table nil x y q t g keyA
  · rcases cycle_of_good_table nil x⁻¹ y (-q) (-t) g keyB with E|E
    · exact Or.inl ((cycle_inv_left x y).mp E)
    · exact Or.inr ((cycle_inv_left x y).mp E)

end Ribbon6
#print axioms Ribbon6.cycle_of_tables
