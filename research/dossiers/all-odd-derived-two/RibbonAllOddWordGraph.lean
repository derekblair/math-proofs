import RibbonAllOddWordData
namespace RibbonAllOddField
open Ribbon5Bridge RibbonDerived3 Ribbon8Free
open RibbonStationaryWord (Spec Valid head Rstr complete_head complete_all mate_ne)
variable {G : Type*} [Group G]

def IsMate (s : Spec) (i j : Nat) : Prop :=
  ∃ m : Fin s.mates.size, s.mates[m].i=i ∧ s.mates[m].j=j
instance (s : Spec) (i j : Nat) : Decidable (IsMate s i j) := by unfold IsMate; infer_instance

theorem mate_late : ∀ (k : Count) (m : Fin (spec k).mates.size),
    32 ≤ (spec k).mates[m].j := by decide +kernel

theorem head_take (s : Spec) (x y : G) (i : Nat) (hi : i≤32) :
    pathAt x y (head s).toArray i = pathAt x y s.T.toArray i := by
  simp [pathAt,head,List.take_take,Nat.min_eq_left hi]

/-- It suffices that every non-mate pair of prefixes is separated by a chart
or by a combination of charts. The mate pairs are certified in the actual group. -/
theorem from_state (dnil : DLS G 2=⊥) (k : Count) (x y : G)
    {X : Type*} (chart : Fin 64 → X)
    (sound : ∀ (i j : Fin 64), pathAt x y (spec k).T.toArray i.val =
      pathAt x y (spec k).T.toArray j.val → chart i = chart j)
    (sep : ∀ (i j : Fin 64), i.val<j.val → chart i = chart j → IsMate (spec k) i.val j.val) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let s := spec k
  have V : Valid s := all_valid k
  by_cases R : ev x y (Rstr s)=1
  · left
    apply cycle_from_at x y (head s).toArray (by simpa [head,List.length_take,V.1]) (complete_head s V x y R)
    intro i j lt E
    rw [head_take s x y i.val i.isLt.le,head_take s x y j.val j.isLt.le] at E
    have i64 : i.val<64 := by have := i.isLt; omega
    have j64 : j.val<64 := by have := j.isLt; omega
    obtain ⟨m,_,hj⟩ := sep ⟨i.val,i64⟩ ⟨j.val,j64⟩ lt (sound _ _ E)
    have h := mate_late k m
    change 32 ≤ s.mates[m].j at h
    rw [hj] at h
    exact (Nat.not_le_of_gt j.isLt) h
  · right
    apply cycle_from_at x y s.T.toArray (by simpa using V.1) (complete_all s V dnil x y)
    intro i j lt E
    obtain ⟨m,hi,hj⟩ := sep i j lt (sound _ _ E)
    exact mate_ne s V x y R m (by rwa [hi,hj])

end RibbonAllOddField
#print axioms RibbonAllOddField.from_state
