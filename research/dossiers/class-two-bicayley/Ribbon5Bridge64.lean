import Ribbon5Walk

namespace Ribbon5Bridge

variable {G : Type*} [Group G]

def W : List P := [1,2,0,0,2,0,2,1,2,1,2,1,2,0,2,0,0,2,1,2,1,2,0,2,1,2]
def T : List P := [0,2,0,0,2,1]

theorem run_append (x y : G) (s : Bool×G) (u v : List P) :
    run x y s (u++v)=run x y (run x y s u) v := by simp [run,List.foldl_append]

def residue (x y : G) : G := (run x y (start G) W).2

private theorem run_W (x y : G) : run x y (start G) W=shift (residue x y) (start G) := by
  apply Prod.ext
  · rfl
  · simp [shift,start,residue]

private theorem run_T (x y : G) :
    run x y (start G) T = shift (run x y (start G) T).2 (start G) := by
  apply Prod.ext
  · rfl
  · simp [shift,start]

private theorem inverse_shift (x y r : G) (w : List P)
    (h : run x y (start G) w=shift r (start G)) :
    run x y (start G) (reverseWord w) = shift r⁻¹ (start G) := by
  have E := undo_run x y (start G) w
  rw [h,shift_run] at E
  apply Prod.ext
  · have e := congrArg (Prod.fst : Bool × G → Bool) E
    exact e
  · have J := congrArg Prod.snd E
    change r*(run x y (start G) (reverseWord w)).2=1 at J
    have Q := congrArg (fun a => r⁻¹*a) J
    rw [← mul_assoc,inv_mul_cancel,one_mul,mul_one] at Q
    simpa only [shift,start,mul_one] using Q

private theorem run_revW (x y : G) : run x y (start G) (reverseWord W) =
    shift ((residue x y)⁻¹) (start G) :=
  inverse_shift x y _ W (run_W x y)

private theorem middle_cancel (x y : G) (cr : ∀ z : G, Commute (residue x y) z) :
    run x y (run x y (run x y (start G) W) T) (reverseWord W) = run x y (start G) T := by
  let s := run x y (start G) T
  rw [run_W,shift_run,shift_run]
  change shift (residue x y) (run x y s (reverseWord W))=s
  have hs : s=shift s.2 (start G) := run_T x y
  rw [hs,shift_run,run_revW]
  apply Prod.ext
  · rfl
  · simp only [shift,start,mul_one]
    rw [←mul_assoc,(cr s.2).eq,mul_assoc,mul_inv_cancel,mul_one]

private theorem layout : word64.toList = W++T++reverseWord W++reverseWord T := by decide +kernel

theorem full_close (x y : G) (cr : ∀ z : G, Commute (residue x y) z) :
    pathAt x y word64 64 = pathAt x y word64 0 := by
  unfold pathAt
  rw [show word64.toList.take 64 = word64.toList from (by decide +kernel),layout]
  simp only [List.take_zero]
  rw [run_append,run_append,run_append,middle_cancel x y cr,undo_run]
  rfl

private theorem layout_early (k : Nat) (hk : k≤6) :
    word64.toList.take (26+k)=W++T.take k := by interval_cases k <;> decide +kernel

private theorem layout_late (k : Nat) (hk : k≤6) :
    word64.toList.take (64-k)=W++T++reverseWord W++reverseWord (T.drop k) :=
  by interval_cases k <;> decide +kernel

theorem early (x y : G) (k : Nat) (hk : k≤6) :
    pathAt x y word64 (26+k) = shift (residue x y) (run x y (start G) (T.take k)) := by
  unfold pathAt
  rw [layout_early k hk,run_append,run_W,shift_run]

theorem late (x y : G) (k : Nat) (hk : k≤6) (cr : ∀ z : G, Commute (residue x y) z) :
    pathAt x y word64 (64-k) = run x y (start G) (T.take k) := by
  unfold pathAt
  rw [layout_late k hk,run_append,run_append,run_append,middle_cancel x y cr]
  have E : run x y (start G) T = run x y (run x y (start G) (T.take k)) (T.drop k) := by
    rw [← run_append,List.take_append_drop]
  rw [E,undo_run]

theorem mate_distinct (x y : G) (cr : ∀ z : G, Commute (residue x y) z)
    (n : residue x y ≠ 1) (i j : Nat) (m : mate i j) :
    pathAt x y word64 i ≠ pathAt x y word64 j := by
  intro E
  rcases m with ⟨rfl,rfl⟩|⟨a,b,c⟩
  · have Q := early x y 0 (by decide)
    have H := congrArg Prod.snd (E.trans Q)
    apply n
    simpa [pathAt,shift,start,run] using H.symm
  · let k := i-26
    have hk : k≤6 := by dsimp [k]; omega
    have iE : i=26+k := by dsimp [k]; omega
    have jE : j=64-k := by dsimp [k]; omega
    rw [iE,jE,early x y k hk,late x y k hk cr] at E
    have H := congrArg Prod.snd E
    change residue x y*(run x y (start G) (T.take k)).2 =
        (run x y (start G) (T.take k)).2 at H
    apply n
    exact mul_right_cancel (H.trans (one_mul _).symm)

end Ribbon5Bridge
#print axioms Ribbon5Bridge.full_close
#print axioms Ribbon5Bridge.mate_distinct
