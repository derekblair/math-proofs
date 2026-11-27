import HeawoodGirthFiftyFour
import HomologyThreeUpper

namespace HeawoodDouble
open HaarDerivedFlowPositive HomologyThree
theorem first_upper : Cyclic Edge1 18 :=
  triple_upper HeawoodGirthSix.Edge 6 (by decide) cycle6
theorem second_upper : Cyclic Edge2 54 :=
  triple_upper Edge1 18 (by decide) first_upper

theorem girth54 : Cyclic Edge2 54 ∧ ∀ n, 3≤n → Cyclic Edge2 n → 54≤n :=
  ⟨second_upper,second_lower⟩

end HeawoodDouble
#print axioms HeawoodDouble.girth54
