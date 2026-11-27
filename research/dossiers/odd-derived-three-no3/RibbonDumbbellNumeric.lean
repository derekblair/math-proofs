import RibbonDumbbellTables

namespace RibbonDumbbell

def allowed (m : Mode) : List Z :=
  ![[0,(1,0),(0,1),(1,1)], [0,(1,0)], [0,(1,0)], [0], [0]] m

def StepOK (m : Mode) (i : Fin (len m)) : Prop :=
  dst (stepDir m i.val) (dot i.val) = site m (next m i).val ∧
  levels m (next m i).val =
    levels m i.val + gain (shiftA m) (shiftB m) (stepDir m i.val) (dot i.val)
instance (m : Mode) (i : Fin (len m)) : Decidable (StepOK m i) := by unfold StepOK; infer_instance

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
theorem step_checked (m : Mode) : ∀ i : Fin (len m), StepOK m i := by
  fin_cases m <;> decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
theorem code_checked (m : Mode) :
    ∀ i : Fin (len m), (table m)[indexCode m i.val]! = i.val := by
  fin_cases m <;> decide +kernel

set_option maxHeartbeats 3000000 in
theorem level_checked (m : Mode) :
    ∀ i : Fin (len m), levels m i.val ∈ allowed m := by
  fin_cases m <;> decide +kernel

theorem reverse_site (d : Dir) (i : Dot) : src d i = dst (alter d) (reverseDot i) := by
  have R : ∀ d : Dir, ∀ i : Dot, src d i = dst (alter d) (reverseDot i) := by decide +kernel
  exact R d i

theorem reverse_end (d : Dir) (i : Dot) : dst d i = src (alter d) (reverseDot i) := by
  have R : ∀ d : Dir, ∀ i : Dot, dst d i = src (alter d) (reverseDot i) := by decide +kernel
  exact R d i

theorem reverse_gain (a b : Z) (d : Dir) (i : Dot) :
    gain a b d i = -gain a b (alter d) (reverseDot i) := by
  have R : (reverseDot i).val = 31-i.val := by
    have hi := i.isLt
    exact Nat.mod_eq_of_lt (by omega)
  have f (k : Nat) (hk : k<32) :
      ((31-i.val) == k) = (i.val == 31-k) := by
    have h := i.isLt
    cases e : (31-i.val == k) <;> cases q : (i.val == 31-k) <;> simp_all [beq_iff_eq] <;> omega
  fin_cases d <;> simp [gain,alter,R,f 0 (by decide),f 31 (by decide)] <;> split_ifs <;> simp

#print axioms step_checked
#print axioms code_checked
end RibbonDumbbell
