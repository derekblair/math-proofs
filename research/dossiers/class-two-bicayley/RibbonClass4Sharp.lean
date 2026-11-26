import RibbonClass4SharpCert
import RibbonClass4SharpHalf
import RibbonClass4SharpUpper

namespace RibbonClass4SharpGraph

theorem sharp :
    ¬ Ribbon.Cycle a b 4 ∧ ¬ Ribbon.Cycle a b 8 ∧ ¬ Ribbon.Cycle a b 16 ∧ Ribbon.Cycle a b 32 :=
  ⟨excluded 2 (by decide) checked2,excluded 4 (by decide) checked4,
    excluded 8 (by decide) checked8,cycle32⟩

end RibbonClass4SharpGraph
#print axioms RibbonClass4SharpGraph.sharp
