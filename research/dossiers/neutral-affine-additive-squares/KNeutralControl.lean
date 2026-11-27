import KNeutralExact
import NeutralReachable

namespace KNeutralControl
open NeutralReachable (D f closed aff lt_iter)
open KNeutralExact (calculate calculate_correct Contains)

theorem reachable_nonuniform_cube : calculate D f 2 closed 3 1 0 1 false 0 (by decide) = true := by
  apply (calculate_correct D f 2 closed 3 1 0 1 false aff (by decide) (by decide)
    0 (by decide) [1,-1] (by decide) (fun n => ⟨n,lt_iter n⟩)).mpr
  refine ⟨2,[0,1,-1,1],[-1,0],(fun _ : Fin 3 => [0]),?_,?_,?_⟩
  · decide
  · intro _; simp
  · intro _; rfl

end KNeutralControl

#print axioms KNeutralControl.reachable_nonuniform_cube
