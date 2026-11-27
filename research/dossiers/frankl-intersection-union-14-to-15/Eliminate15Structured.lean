import Eliminate15TreeData
import VertexFast

namespace IU.IU15Tree
open IU.Eliminate
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def Outer (a : Nat) : Prop :=
  rank a 6 ≤ 3 ∨ 4 ≤ rank a 15 - rank a 7

instance (a : Nat) : Decidable (Outer a) := by unfold Outer; infer_instance

def Init (a : Nat) : Prop :=
  ∃ r ∈ maxRows 0 (rank a 15), Dominates 15 r.a a

instance (a : Nat) : Decidable (Init a) := by unfold Init; infer_instance

def stage (a : Nat) : Nat := if Init a then 0 else if Outer a then 1 else 2
def selected (a : Nat) : Bool := ((maxRows (stage a) (rank a 15)).map Row.a).contains a
def phase (a : Nat) : Nat := 2 * stage a + (if selected a then 0 else 1)

private theorem stages_mono {a b : Nat} (h : phase a≤phase b) : stage a≤stage b := by
  unfold phase at h
  split at h <;> (split at h <;> omega)

def piv (k : Nat) : Nat :=
  match k with
  | 2 => 3
  | 3 => 7
  | 4 => 71
  | 5 => 199
  | 6 => 455
  | 7 => 967
  | 8 => 1935
  | 9 => 1951
  | 10 => 1983
  | 11 => 2047
  | 12 => 4095
  | 13 => 8191
  | _ => 0

theorem piv_dominates {a k : Nat} (ka : rank a 15=k) (H : Outer a)
    (persist : rank (piv k) 15=k ∧
      (∀ t ∈ List.range 16, rank (piv k) t =
        if k≤7 then envelope k 6 3 t else envelope k 7 (k-4) t)) :
    Dominates 15 (piv k) a := by
  have L := (outsider_cap (a:=a) (n:=15) (l:=3) (r:=4) ka (by decide)).mp (by simpa [Outer,ka] using H)
  by_cases s : k≤7
  · refine cap_domination ka (by simpa [s] using L) persist.1 ?_
    intro t ht
    simpa [s] using persist.2 t ht
  · refine cap_domination ka (by simpa [s] using L) persist.1 ?_
    intro t ht
    simpa [s] using persist.2 t ht

theorem class_nonescalating {a r : Nat} (sa : stage a = stage r)
    (sel : selected r=true)
    (uniq : selected a=true → r=a) :
    ∀ b, b ≠ a → phase a ≤ phase b → b ≠ r ∧ stage r ≤ stage b := by
  intro b bn h
  refine ⟨?_,sa ▸ stages_mono h⟩
  intro e
  by_cases selA : selected a = true
  · exact bn (e.trans (uniq selA))
  · rw [e] at h
    have selA' := Bool.eq_false_iff.mpr selA
    simp only [phase,sa,selA',sel,Bool.false_eq_true,ite_false,ite_true] at h
    omega

def RowIsSound (s k : Nat) (row : Row 4106) : Prop :=
  rank row.a 15=k ∧ stage row.a=s ∧ rowOk 15 2 2 4092 colors stage row

instance (s k : Nat) (row : Row 4106) : Decidable (RowIsSound s k row) := by
  unfold RowIsSound
  infer_instance

theorem use_row {a s k : Nat} {row : Row 4106}
    (sa : stage a = s) (_ka : rank a 15 = k)
    (R : row∈maxRows s k) (sound : RowIsSound s k row)
    (d : Dominates 15 row.a a) (U : selected a = true → row.a=a) :
    ∃ miss : Finset (Fin 4106), 4106 - miss.card < 4092 ∧
      ∀ i∈miss, ∀ b∈colors i, b ≠ a → phase a ≤ phase b → edge 15 2 2 a b = false := by
  have sr : selected row.a=true := by
    unfold selected
    rw [sound.1,sound.2.1,List.contains_iff_mem]
    exact List.mem_map.mpr ⟨row,R,rfl⟩
  exact certificate_of_dom sound.2.2 d (class_nonescalating (sa.trans sound.2.1.symm) sr U)

theorem choose_row_of_selected {a : Nat} (h : selected a=true) :
    ∃ row∈maxRows (stage a) (rank a 15), row.a=a := by
  rw [selected,List.contains_iff_mem] at h
  exact List.mem_map.mp h

def PivotFacts (k : Nat) : Prop :=
    (rank (piv k) 15=k ∧ (∀ t ∈ List.range 16, rank (piv k) t =
        if k≤7 then envelope k 6 3 t else envelope k 7 (k-4) t)) ∧
      (∃ row ∈ maxRows 0 k, row.a=piv k) ∨
    (rank (piv k) 15=k ∧ (∀ t ∈ List.range 16, rank (piv k) t =
        if k≤7 then envelope k 6 3 t else envelope k 7 (k-4) t)) ∧
      (∃ row ∈ maxRows 1 k, row.a=piv k)

instance (k : Nat) : Decidable (PivotFacts k) := by unfold PivotFacts; infer_instance

theorem structured_rows (R : ∀ s k, ∀ row∈maxRows s k, RowIsSound s k row)
    (P : ∀ k, 2 ≤ k → k ≤ 13 → PivotFacts k)
    {a : Nat} (amin : 2≤rank a 15) (amax : rank a 15≤13) (st : stage a < 2) :
    ∃ miss : Finset (Fin 4106), 4106 - miss.card < 4092 ∧
      ∀ i∈miss, ∀ b∈colors i, b ≠ a → phase a ≤ phase b → edge 15 2 2 a b = false := by
  by_cases h : selected a = true
  · obtain ⟨r,rm,rEq⟩ := choose_row_of_selected h
    apply use_row rfl rfl rm (R _ _ _ rm) _ (fun _ => rEq)
    rw [rEq]
    exact ⟨rfl,fun _ _ => le_rfl⟩
  by_cases aIn : Init a
  · have st0 : stage a=0 := by simp [stage,aIn]
    obtain ⟨r,rm,d⟩ := aIn
    exact use_row st0 rfl rm (R _ _ _ rm) d (fun z => (h z).elim)
  have aOut : Outer a := by
    by_contra z
    simp [stage,aIn,z] at st
  have st1 : stage a=1 := by simp [stage,aIn,aOut]
  have pf := P _ amin amax
  rcases pf with ⟨f,⟨r,rm,rv⟩⟩ | ⟨f,⟨r,rm,rv⟩⟩
  · have D := piv_dominates rfl aOut f
    exact False.elim (aIn ⟨r,rm,by simpa [rv] using D⟩)
  · have D := piv_dominates rfl aOut f
    exact use_row st1 rfl rm (R _ _ _ rm) (by simpa [rv] using D) (fun z => (h z).elim)

end IU.IU15Tree
