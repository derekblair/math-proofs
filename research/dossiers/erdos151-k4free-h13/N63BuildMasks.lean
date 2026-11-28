import N63FastCode
import N63RightBits

namespace Erdos151N63

def mixedBits (j : Nat) (ts : List Nat) : Nat :=
  (ts.zipIdx).foldl (fun a (m,i) => if m.testBit j then a ||| (1 <<< (i+1)) else a) 0

theorem mixedBits_fold (j k r : Nat) (A : List (Nat×Nat)) :
    (A.foldl (fun a (m,i) => if m.testBit j then a ||| (1 <<< (i+1)) else a) r).testBit k =
    (r.testBit k || A.any (fun (m,i) => m.testBit j && i+1==k)) := by
  induction A generalizing r with
  | nil => simp
  | cons a A ih =>
    rcases a with ⟨m,i⟩
    rw [List.foldl_cons, ih]
    have hbeq : (i+1 == k) = decide (i+1=k) := by
      apply Bool.eq_iff_iff.mpr
      simp
    cases h : m.testBit j <;> by_cases e : i+1=k <;>
      simp [h,e,hbeq,Nat.shiftLeft_eq,Nat.testBit_two_pow,Bool.or_assoc]

theorem mixedBits_read (j i : Nat) (ts : List Nat) :
    (mixedBits j ts).testBit (i+1) = (ts[i]?.getD 0).testBit j := by
  rw [mixedBits,mixedBits_fold]
  simp only [Nat.zero_testBit,Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a,k⟩,hk,hh⟩
    simp only [Bool.and_eq_true,beq_iff_eq,Nat.add_right_cancel_iff] at hh
    obtain ⟨ha,rfl⟩ := hh
    rw [List.mk_mem_zipIdx_iff_getElem?.mp hk]
    exact ha
  · intro h
    cases hk : ts[i]? with
    | none => simp [hk] at h
    | some a =>
      exact ⟨(a,i),List.mk_mem_zipIdx_iff_getElem?.mpr hk,by simpa [hk] using h⟩

theorem mixedBits_off (j k : Nat) (ts : List Nat) (h : ts.length < k ∨ k=0) :
    (mixedBits j ts).testBit k = false := by
  rw [mixedBits,mixedBits_fold]
  simp only [Nat.zero_testBit,Bool.false_or]
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  obtain ⟨⟨a,i⟩,hi,he⟩ := List.any_eq_true.mp htrue
  have hlt := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)).1
  simp only [Bool.and_eq_true,beq_iff_eq] at he
  omega

theorem buildMask_zero (d q : Nat) (H : Array Nat) (ts : List Nat) :
    mask (buildRaw d q H ts) 0 = (1 <<< (d+1))-2 := by
  simp [mask,buildRaw]

theorem buildMask_left (d q : Nat) (H : Array Nat) (ts : List Nat) (i : Nat) (hi : i < ts.length) :
    mask (buildRaw d q H ts) (i+1) = 1 ||| ((ts[i]?.getD 0) <<< (d+1)) := by
  unfold mask buildRaw
  simp only [List.getElem?_toArray, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simp [hi])]
  simp [List.getElem?_eq_getElem hi]

theorem buildMask_right (d q : Nat) (H : Array Nat) (ts : List Nat)
    (hD : ts.length=d) (j : Nat) (hj : j<q) :
    mask (buildRaw d q H ts) (d+1+j) = mixedBits j ts ||| (mask H j <<< (d+1)) := by
  unfold mask buildRaw
  rw [show d+1+j = (d+j)+1 by omega]
  simp only [List.getElem?_toArray,List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp [hD])]
  simp [hD,hj,mixedBits,mask]

#print axioms buildMask_right
#print axioms mixedBits_read

theorem buildAdj_pivot (d q : Nat) (H : Array Nat) (ts : List Nat) (k : Nat) :
    adj (buildRaw d q H ts) 0 k = decide (1 ≤ k ∧ k ≤ d) := by
  rw [adj,buildMask_zero]
  have hh : (1 <<< (d+1))-2 = (2^d-1) <<< 1 := by
    rw [Nat.shiftLeft_eq,Nat.shiftLeft_eq,Nat.one_mul,Nat.pow_succ]
    have hp := Nat.two_pow_pos d
    omega
  rw [hh,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.mpr
  simp
  omega

theorem buildAdj_left (d q : Nat) (H : Array Nat) (ts : List Nat)
    (hD : ts.length=d) (i k : Nat) (hi : i<d) :
    adj (buildRaw d q H ts) (i+1) k =
      (decide (k=0) || (decide (d+1≤k) && (ts[i]?.getD 0).testBit (k-(d+1)))) := by
  rw [adj,buildMask_left _ _ _ _ _ (by omega), Nat.testBit_or,Nat.testBit_shiftLeft]
  have hh : (1:Nat) = 2^0 := rfl
  rw [hh,Nat.testBit_two_pow]
  simp [eq_comm]

theorem buildAdj_right (d q : Nat) (H : Array Nat) (ts : List Nat)
    (hD : ts.length=d) (j k : Nat) (hj : j<q) :
    adj (buildRaw d q H ts) (d+1+j) k =
      ((mixedBits j ts).testBit k || (decide (d+1≤k) && adj H j (k-(d+1)))) := by
  rw [adj,buildMask_right _ _ _ _ hD _ hj,Nat.testBit_or,Nat.testBit_shiftLeft]
  rfl

#print axioms buildAdj_pivot
#print axioms buildAdj_left
#print axioms buildAdj_right
end Erdos151N63
