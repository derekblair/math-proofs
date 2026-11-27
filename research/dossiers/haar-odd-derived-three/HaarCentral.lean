import HaarBound16
import HaarAbel
import HaarSharpGraph

namespace HaarCentral
open HaarAllNoncommuting

theorem dyadic_cycle {G : Type*} [Group G] (x y z : G)
    (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (cx : Commute z x) (cy : Commute z y) (rel : x*y=y*x*z) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 := by
  by_cases e : z=1
  · have h : Commute x y := by change x*y=y*x; simpa [e] using rel
    exact HaarAbel.commute_case x y h hx hy hxy
  · exact HaarBound16.sharpened x y z cx cy rel e

theorem example_requires_sixteen :
    HasCycle HaarSharpCore.x HaarSharpCore.y 16 ∧
    ¬HasCycle HaarSharpCore.x HaarSharpCore.y 4 ∧
    ¬HasCycle HaarSharpCore.x HaarSharpCore.y 8 :=
  HaarSharpGraph.sharp

theorem sharp_example_not_girth_six :
    ¬ HasCycle HaarSharpCore.x HaarSharpCore.y 6 :=
  HaarSharpGraph.no_cycle 6 (Or.inr (Or.inl rfl))

end HaarCentral
#print axioms HaarCentral.dyadic_cycle
#print axioms HaarCentral.example_requires_sixteen
#print axioms HaarCentral.sharp_example_not_girth_six
