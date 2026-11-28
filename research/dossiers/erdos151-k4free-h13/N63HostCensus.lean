import N63HostNormalize
import N63CodeBinding
namespace Erdos151N63
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V→V→Prop) [DecidableRel G]

theorem nine_complete_host (hn : Fintype.card V=9)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (hmin : ∀ v, 2 ≤ fullDeg G v)
    (dense : 28 ≤ ∑ v : V, fullDeg G v) :
    ∃ (e : Entry) (relabel : Fin 9 ≃ V), e.Check 9 ∧
      ∀ i j : Fin 9, adj e.rows i.val j.val = true ↔ G (relabel i) (relabel j) :=
  nine_host_of_code_binding G bind_all_codes hn sym irr tf hmin dense

#print axioms nine_complete_host
end Erdos151N63
