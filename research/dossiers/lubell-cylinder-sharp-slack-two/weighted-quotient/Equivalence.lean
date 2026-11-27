import Compact
namespace IU.Slack

def ExactOriginal (w : Nat → Nat) (t u s M : Nat) : Prop :=
  (∀ F : Sys, IsIU F (t+u+s) t u → objective w F≤M) ∧
  ∃ F : Sys, IsIU F (t+u+s) t u ∧ objective w F=M

def ExactQuotient (w : Nat → Nat) (t u s M : Nat) : Prop :=
  (∀ I : Finset Q, Good I t u s → Qscore w I t u≤M) ∧
  ∃ I : Finset Q, Good I t u s ∧ Qscore w I t u=M

/-- The bounded profile graph preserves the exact optimum, including
attainment, for every nonnegative integral layer weight. -/
theorem exact_iff (w : Nat → Nat) {t u s M : Nat} (ht : 0<t) :
    ExactOriginal w t u s M ↔ ExactQuotient w t u s M := by
  constructor
  · rintro ⟨up,F,Fok,fscore⟩
    have qup (I : Finset Q) (g : Good I t u s) : Qscore w I t u≤M := by
      rw [←lift_score w g]
      exact up _ (lift_valid g)
    obtain ⟨I,g,le⟩ := original_to_graph w F ht Fok
    rw [fscore] at le
    exact ⟨qup,I,g,le_antisymm (qup I g) le⟩
  · rintro ⟨up,I,g,iscore⟩
    refine ⟨?_,lift I t u s,lift_valid g,(lift_score w g).trans iscore⟩
    intro F Fok
    obtain ⟨J,G,le⟩ := original_to_graph w F ht Fok
    exact le.trans (up J G)

#print axioms exact_iff
end IU.Slack
