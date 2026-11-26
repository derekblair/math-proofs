import PetersenSharpScan
import PetersenSharpWitness
import PetersenBaseId

namespace PetersenSharp
theorem identifies_base (u v : B) : baseEdge u v ↔ PetersenWalkData.base u v := by
  change (∃ p : P, base u p = v) ↔ PetersenWalkData.base u v
  decide +revert


theorem sharp : ¬ Cyclic 4 ∧ ¬ Cyclic 8 ∧ Cyclic 16 :=
  ⟨no4,no8,cycle16⟩

end PetersenSharp

#print axioms PetersenSharp.sharp
#print axioms PetersenSharp.identifies_base
