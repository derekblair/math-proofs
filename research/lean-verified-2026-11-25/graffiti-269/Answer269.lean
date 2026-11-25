import C4_269
import Sum269

open SimpleGraph
namespace Refute269

def portals : Finset Big := {P 0, P 1, P 2, P 3}

lemma hp_mem (p : Fin 4) : P p ∈ portals := by fin_cases p <;> decide

lemma hp_card : portals.card = 4 := by decide

lemma td : Wow268.TotalDominating G portals := by
  intro v
  rcases v with p | (⟨i,r⟩ | ⟨i,r⟩)
  · fin_cases p
    · exact ⟨P 1, hp_mem _, by decide⟩
    · exact ⟨P 0, hp_mem _, by decide⟩
    · exact ⟨P 3, hp_mem _, by decide⟩
    · exact ⟨P 2, hp_mem _, by decide⟩
  · exact ⟨P (ap r), hp_mem _, rfl⟩
  · exact ⟨P (bp r), hp_mem _, rfl⟩

lemma gamma_le : Wow268.gammaT G conn ≤ 4 := by
  classical
  unfold Wow268.gammaT
  exact Nat.find_min' _ ⟨portals, hp_card, td⟩

lemma gamma_eq : Wow268.gammaT G conn = 4 := by
  have h := Wow268.conjecture268 G conn
  rw [avg_exact] at h
  have hc : ⌊(1 : ℚ) + 17890 / 5963⌋ = 4 := by
    exact Int.floor_eq_iff.mpr (by norm_num)
  rw [hc] at h
  exact le_antisymm gamma_le (by exact_mod_cast h)

lemma ceil_exact : ⌈1 + Wow268.avg G⌉ = (5 : ℤ) := by
  rw [avg_exact]
  exact Int.ceil_eq_iff.mpr (by norm_num)

/-- Exact finite-graph form of Written on the Wall II, Conjecture 269. -/
def Conjecture269 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
    (H : SimpleGraph V) (hc : H.Connected),
    C4Free H → ⌈1 + Wow268.avg H⌉ ≤ (Wow268.gammaT H hc : ℤ)

/-- Concrete failure of the asserted inequality, using an equivalent finite vertex type. -/
theorem counterexample :
    G.Connected ∧ C4Free G ∧ Wow268.gammaT G conn = 4 ∧ ⌈1 + Wow268.avg G⌉ = (5 : ℤ) ∧
      (Wow268.gammaT G conn : ℤ) < ⌈1 + Wow268.avg G⌉ := by
  refine ⟨conn, no4, gamma_eq, ceil_exact, ?_⟩
  rw [gamma_eq, ceil_exact]
  decide

/-- Refutes the catalogue statement universally quantified over finite vertex types. -/
theorem not_graffiti269 : ¬ Conjecture269 := by
  intro h
  exact (not_le_of_gt counterexample.2.2.2.2) (h Big G conn no4)

#print axioms not_graffiti269
#print axioms counterexample
end Refute269
