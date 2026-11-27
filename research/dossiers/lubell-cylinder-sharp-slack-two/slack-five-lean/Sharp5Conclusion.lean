import Sharp5BridgeCore
import Sharp5Grid0Final
import Sharp5Grid1Final
import Sharp5Grid2Final

namespace IU.Sharp5
open IU.Slack

theorem sharp_five_ordered {t u : Nat} (ht : 0<t) (hu : 2≤u) (hle : t≤u) :
    (∃ F : IU.Sys, IU.IsIU F (t+u+5) t u ∧ rawSum (t+u+5) F=optimum t u) ∧
    ∀ F : IU.Sys, IU.IsIU F (t+u+5) t u → rawSum (t+u+5) F≤optimum t u :=
  sharp_five_ordered_of_cones Cone0.checked Cone1.checked Cone2.checked ht hu hle

#print axioms sharp_five_ordered
end IU.Sharp5
