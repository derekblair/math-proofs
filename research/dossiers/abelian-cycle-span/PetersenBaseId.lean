import PetersenWalkData

namespace PetersenBaseId
open PetersenWalkData
def forward (a b : Fin 10) : Prop :=
  (a.val<5 ∧ b.val=(a.val+1)%5) ∨
  (5≤a.val ∧ b.val=5+(a.val-5+2)%5) ∨
  (a.val<5 ∧ b.val=a.val+5)
instance (a b : Fin 10) : Decidable (forward a b) := by
  unfold forward
  infer_instance
instance (a b : Fin 10) : Decidable (base a b) := by
  unfold base
  infer_instance
theorem identifies (a b : Fin 10) : base a b ↔ forward a b ∨ forward b a := by
  revert a b
  decide +kernel
end PetersenBaseId
#print axioms PetersenBaseId.identifies
