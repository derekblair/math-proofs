import N63Exception
namespace Erdos151N63
set_option maxHeartbeats 0

theorem chart83_shape :
    (∀ i j : Fin 9, adj chart83 i.val j.val = adj chart83 j.val i.val) ∧
    (∀ i : Fin 9, adj chart83 i.val i.val = false) ∧
    (∀ i : Fin 9, deg chart83 9 i.val = if i.val = 8 then 4 else 3) ∧
    (∀ i : Fin 9, adj chart83 8 i.val = true ↔ i.val ∈ common83) := by decide +kernel

theorem chart88_shape :
    (∀ i j : Fin 9, adj chart88 i.val j.val = adj chart88 j.val i.val) ∧
    (∀ i : Fin 9, adj chart88 i.val i.val = false) ∧
    (∀ i : Fin 9, deg chart88 9 i.val = if i.val = 6 then 4 else 3) ∧
    (∀ i : Fin 9, adj chart88 6 i.val = true ↔ i.val ∈ common88) := by decide +kernel

#print axioms chart83_shape
#print axioms chart88_shape
end Erdos151N63
