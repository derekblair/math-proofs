import Seed64Numeric
import Seed64Assemble

namespace Erdos151Ramsey.Seed64
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem alpha_le_thirteen (S : Finset (Fin 63)) (ind : Independent graph S) : S.card ≤ 13 :=
  alpha_of_checked checked_root S ind

theorem ramsey314_ge64 :
    ∃ R : Fin 63 → Fin 63 → Prop, (∀ {a b}, R a b → R b a) ∧ (∀ a, ¬ R a a) ∧
      TriangleFree R ∧ (∀ S : Finset (Fin 63), Independent R S → S.card ≤ 13) :=
  ramsey314_of_checked checked_root

theorem not_universal14 :
    ¬ (∀ R : Fin 63 → Fin 63 → Prop, (∀ {a b}, R a b → R b a) → (∀ a, ¬ R a a) →
      TriangleFree R → ∃ S : Finset (Fin 63), 14 ≤ S.card ∧ Independent R S) :=
  not_universal14_of_checked checked_root

#print axioms ramsey314_ge64
#print axioms not_universal14
end Erdos151Ramsey.Seed64
