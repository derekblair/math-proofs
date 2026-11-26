import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

namespace DirectedFailurePaths

/-- Among tags with distinct codes, one bit per better tag suffices to
force a desired tag to win, by restricting each selected bit to its value
on the desired tag. The lemma does not claim an APSP engine or time bound. -/
theorem isolate_tag {T : Type*} {bits : Nat} (code : T → Fin bits → Bool)
    (inj : Function.Injective code) (wanted : T) (better : List T)
    (excludes : ∀ e ∈ better, e ≠ wanted) :
    ∃ mask : List (Fin bits), mask.length ≤ better.length ∧
      (∀ j ∈ mask, code wanted j = code wanted j) ∧
      ∀ e ∈ better, ∃ j ∈ mask, code e j ≠ code wanted j := by
  classical
  induction better with
  | nil =>
    exact ⟨[],by simp,fun _ _ => rfl, by simp⟩
  | cons e l ih =>
    have N := excludes e List.mem_cons_self
    have C : code e ≠ code wanted := inj.ne N
    have B : ∃ j, code e j ≠ code wanted j := by
      by_contra H
      push Not at H
      exact C (funext H)
    obtain ⟨j,J⟩ := B
    obtain ⟨mask,len,_,reject⟩ := ih (fun a h => excludes a (List.mem_cons_of_mem _ h))
    refine ⟨j::mask,?_,fun _ _ => rfl,?_⟩
    · simpa using Nat.succ_le_succ len
    · intro a h
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨j,List.mem_cons_self,J⟩
      · obtain ⟨k,hk,K⟩ := reject a h
        exact ⟨k,List.mem_cons_of_mem _ hk,K⟩

end DirectedFailurePaths
#print axioms DirectedFailurePaths.isolate_tag
