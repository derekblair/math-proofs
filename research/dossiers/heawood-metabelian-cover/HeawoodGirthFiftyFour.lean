import HeawoodGirthSix

namespace HeawoodDouble
open HaarOrbitC7Voltage (B)
open HaarDerivedFlowPositive HomologyThree
open HeawoodGirthSix (Edge)
abbrev V1 := B × Lamp B
abbrev V2 := V1 × Lamp V1
abbrev Edge1 := liftEdge Edge
abbrev Edge2 := liftEdge Edge1

theorem first_noloop (u : V1) : ¬ Edge1 u u := fun h => HeawoodGirthSix.no_loop u.1 h.1
theorem first_symm {u v : V1} (h : Edge1 u v) : Edge1 v u := liftSymm Edge HeawoodGirthSix.symm h

theorem first_lower (n : ℕ) (hn : 3≤n) (C : Cyclic Edge1 n) : 18≤n :=
  triple_lower Edge HeawoodGirthSix.symm HeawoodGirthSix.no_loop 3 HeawoodGirthSix.lower n hn C

theorem second_lower (n : ℕ) (hn : 3≤n) (C : Cyclic Edge2 n) : 54≤n :=
  triple_lower Edge1 first_symm first_noloop 9 first_lower n hn C

def six : Fin 6 → B := ![0,7,6,13,5,8]

theorem cycle6 : Cyclic Edge 6 := by
  refine ⟨six,?_,?_⟩
  · unfold Function.Injective; decide +kernel
  · decide +kernel

end HeawoodDouble
#print axioms HeawoodDouble.second_lower
#print axioms HeawoodDouble.cycle6
