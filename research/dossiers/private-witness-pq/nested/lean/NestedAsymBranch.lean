import NestedExposureFast

namespace NestedExposure

def asymFirst (s a : Nat) : Bool :=
  if a ≤ min 13 ((63-s)/9) then
    fastScan (asymAccept s) 8 (63-s-a) a (advance Moments.empty a)
  else true

theorem asym_first_complete (s : Nat)
    (each : ∀ a : Fin 8, asymFirst s a.val=true) :
    fastScan (asymAccept s) 9 (63-s) 0 Moments.empty=true := by
  have left0 : max 0 (63-s-13*8)=0 := by omega
  let hi := min 13 ((63-s)/9)
  have hhi : hi ≤ 7 := by unfold hi; omega
  have bounds :
      (List.range (hi+1)).all (fun a => fastScan (asymAccept s) 8 (63-s-a) a (advance Moments.empty a))=true := by
    apply List.all_eq_true.mpr
    intro a ha
    have ha' : a < hi+1 := List.mem_range.mp ha
    have r : a≤hi := by omega
    have h := each ⟨a,by omega⟩
    change asymFirst s a = true at h
    unfold asymFirst at h
    rw [if_pos r] at h
    exact h
  rw [fastScan,left0,Nat.sub_zero]
  simpa only [Nat.zero_add] using bounds

#print axioms asym_first_complete
end NestedExposure
