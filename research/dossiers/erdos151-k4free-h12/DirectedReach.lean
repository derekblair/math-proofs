import DirectedEvenSink
import Mathlib.Data.Nat.Find

namespace Erdős151.H12
variable {V : Type*}

inductive Steps (R : V → V → Prop) : Nat → V → V → Prop
  | zero (v : V) : Steps R 0 v v
  | more {n x y z} : R x y → Steps R n y z → Steps R (n+1) x z

theorem reach_alternating_root (R : V → V → Prop) (P : V → Prop)
    (base : V → Bool)
    (onRoot : ∀ v, P v → ∃ w, R v w ∧ P w ∧ base v ≠ base w)
    (reachable : ∀ v, ∃ n w, P w ∧ Steps R n v w) :
    ∃ c : V → Bool, ∀ v, ∃ w, R v w ∧ c v ≠ c w := by
  classical
  let r := fun v => Nat.find (reachable v)
  have spec (v : V) : ∃ w, P w ∧ Steps R (r v) v w := Nat.find_spec (reachable v)
  have r0 (v : V) : r v = 0 ↔ P v := by
    constructor
    · intro h
      obtain ⟨w,hw,hpath⟩ := spec v
      rw [h] at hpath
      cases hpath
      exact hw
    · intro h
      have hh := Nat.find_min' (reachable v) (show ∃ w, P w ∧ Steps R 0 v w from ⟨v,h,Steps.zero v⟩)
      exact Nat.eq_zero_of_le_zero hh
  have out (v : V) : ∃ w, R v w ∧
      (r v = 0 → r w = 0 ∧ base v ≠ base w) ∧
      (r v ≠ 0 → r w < r v) := by
    by_cases h : r v = 0
    · obtain ⟨w,e,hw,hb⟩ := onRoot v ((r0 v).mp h)
      exact ⟨w,e,fun _ => ⟨(r0 w).mpr hw,hb⟩,fun nn => False.elim (nn h)⟩
    · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero h
      obtain ⟨w,hw,path⟩ := spec v
      rw [hj] at path
      cases path with
      | more e rest =>
        have hmin := Nat.find_min' (reachable _) ⟨w,hw,rest⟩
        exact ⟨_,e,fun bad => False.elim (h bad),fun _ => by
          change r _ ≤ j at hmin
          omega⟩
  let next := fun v => Classical.choose (out v)
  have hs v := Classical.choose_spec (out v)
  have hn v : R v (next v) := (hs v).1
  have hz v := (hs v).2.1
  have hd v := (hs v).2.2
  obtain ⟨c,hc⟩ := ranked_two_color r next hd base hz
  exact ⟨c,fun v => ⟨next v,hn v,hc v⟩⟩

#print axioms reach_alternating_root
end Erdős151.H12
