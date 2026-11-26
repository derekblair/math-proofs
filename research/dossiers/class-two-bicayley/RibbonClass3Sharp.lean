import RibbonClass3SharpCert
import RibbonClass3SharpHalf
import RibbonClass3SharpUpper

namespace RibbonClass3SharpGraph

theorem class_exact : HaarClass4Structure.LS H 3 = ⊥ ∧ HaarClass4Structure.LS H 2 ≠ ⊥ := by
  refine ⟨class_three,?_⟩
  intro h
  have E := HaarClass4Ports.layer_v a b
  rw [h,Subgroup.mem_bot] at E
  exact picked E

theorem sharp :
    ¬ Ribbon.Cycle a b 4 ∧ ¬ Ribbon.Cycle a b 8 ∧ ¬ Ribbon.Cycle a b 16 ∧ Ribbon.Cycle a b 32 := by
  exact ⟨excluded 2 (by decide) checked2,excluded 4 (by decide) checked4,
    excluded 8 (by decide) checked8,cycle32⟩

end RibbonClass3SharpGraph
#print axioms RibbonClass3SharpGraph.sharp
#print axioms RibbonClass3SharpGraph.class_exact
