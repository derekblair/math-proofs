import Pack

namespace CoverCutoff

def fastEdge {n : ℕ} (preds : List (List ℕ)) (a b : Fin n) : Bool :=
  (preds[b.val]?.getD []).contains a.val

def checkPairs {n : ℕ} (p : Fin n→Fin n→Bool) : Bool :=
  (List.finRange n).all fun a => (List.finRange n).all (p a)

lemma checkPairs_true {n : ℕ} {p : Fin n→Fin n→Bool} (h : checkPairs p = true) (a b : Fin n) :
    p a b = true := by
  have h1 := List.all_eq_true.mp h a (List.mem_finRange a)
  exact List.all_eq_true.mp h1 b (List.mem_finRange b)

def patternA : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def predsA1 : List (List ℕ) := [[], [2], [0], [1]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA1 : ∀ a b : Fin 4, edges patternA.symm 2 1 a b = fastEdge predsA1 a b := by
  have h : checkPairs (fun (a b : Fin 4) => edges patternA.symm 2 1 a b ==
      fastEdge predsA1 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA1 : countSearch (fastEdge predsA1 : Fin 4→Fin 4→Bool) 4 (List.finRange 4) = 1 := by
  decide +kernel

lemma numA1 : packCount patternA 2 1 = 1 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 1 = fastEdge predsA1 by funext a b; exact edgeA1 a b]
  exact execA1

def predsA2 : List (List ℕ) := [[], [2], [0], [1, 4], [2], [3]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA2 : ∀ a b : Fin 6, edges patternA.symm 2 2 a b = fastEdge predsA2 a b := by
  have h : checkPairs (fun (a b : Fin 6) => edges patternA.symm 2 2 a b ==
      fastEdge predsA2 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA2 : countSearch (fastEdge predsA2 : Fin 6→Fin 6→Bool) 6 (List.finRange 6) = 2 := by
  decide +kernel

lemma numA2 : packCount patternA 2 2 = 2 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 2 = fastEdge predsA2 by funext a b; exact edgeA2 a b]
  exact execA2

def predsA3 : List (List ℕ) := [[], [2], [0], [1, 4], [2], [3, 6], [4], [5]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA3 : ∀ a b : Fin 8, edges patternA.symm 2 3 a b = fastEdge predsA3 a b := by
  have h : checkPairs (fun (a b : Fin 8) => edges patternA.symm 2 3 a b ==
      fastEdge predsA3 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA3 : countSearch (fastEdge predsA3 : Fin 8→Fin 8→Bool) 8 (List.finRange 8) = 5 := by
  decide +kernel

lemma numA3 : packCount patternA 2 3 = 5 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 3 = fastEdge predsA3 by funext a b; exact edgeA3 a b]
  exact execA3

def predsA4 : List (List ℕ) := [[], [2], [0], [1, 4], [2], [3, 6], [4], [5, 8], [6], [7]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA4 : ∀ a b : Fin 10, edges patternA.symm 2 4 a b = fastEdge predsA4 a b := by
  have h : checkPairs (fun (a b : Fin 10) => edges patternA.symm 2 4 a b ==
      fastEdge predsA4 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA4 : countSearch (fastEdge predsA4 : Fin 10→Fin 10→Bool) 10 (List.finRange 10) = 14 := by
  decide +kernel

lemma numA4 : packCount patternA 2 4 = 14 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 4 = fastEdge predsA4 by funext a b; exact edgeA4 a b]
  exact execA4

def predsA5 : List (List ℕ) := [[], [2], [0], [1, 4], [2], [3, 6], [4], [5, 8], [6], [7, 10], [8], [9]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA5 : ∀ a b : Fin 12, edges patternA.symm 2 5 a b = fastEdge predsA5 a b := by
  have h : checkPairs (fun (a b : Fin 12) => edges patternA.symm 2 5 a b ==
      fastEdge predsA5 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA5 : countSearch (fastEdge predsA5 : Fin 12→Fin 12→Bool) 12 (List.finRange 12) = 42 := by
  decide +kernel

lemma numA5 : packCount patternA 2 5 = 42 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 5 = fastEdge predsA5 by funext a b; exact edgeA5 a b]
  exact execA5

def predsA6 : List (List ℕ) := [[], [2], [0], [1, 4], [2], [3, 6], [4], [5, 8], [6], [7, 10], [8], [9, 12], [10], [11]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeA6 : ∀ a b : Fin 14, edges patternA.symm 2 6 a b = fastEdge predsA6 a b := by
  have h : checkPairs (fun (a b : Fin 14) => edges patternA.symm 2 6 a b ==
      fastEdge predsA6 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execA6 : countSearch (fastEdge predsA6 : Fin 14→Fin 14→Bool) 14 (List.finRange 14) = 132 := by
  decide +kernel

lemma numA6 : packCount patternA 2 6 = 132 := by
  rw [pack_count_exec]
  rw [show edges patternA.symm 2 6 = fastEdge predsA6 by funext a b; exact edgeA6 a b]
  exact execA6

def patternB : Equiv.Perm (Fin 16) where
  toFun := ![4, 0, 11, 6, 1, 12, 7, 2, 13, 8, 3, 14, 9, 5, 15, 10]
  invFun := ![1, 4, 7, 10, 0, 13, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def predsB1 : List (List ℕ) := [[10], [], [15], [13], [1], [2], [3], [4], [5], [6], [7], [8], [9], [0], [11], [12]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB1 : ∀ a b : Fin 16, edges patternB.symm 3 1 a b = fastEdge predsB1 a b := by
  have h : checkPairs (fun (a b : Fin 16) => edges patternB.symm 3 1 a b ==
      fastEdge predsB1 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB1 : countSearch (fastEdge predsB1 : Fin 16→Fin 16→Bool) 16 (List.finRange 16) = 1 := by
  decide +kernel

lemma numB1 : packCount patternB 3 1 = 1 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 1 = fastEdge predsB1 by funext a b; exact edgeB1 a b]
  exact execB1

def predsB2 : List (List ℕ) := [[10], [], [15], [13], [1], [2, 18], [3, 16], [4], [5], [6], [7], [8], [9], [0, 10], [11], [12], [3], [14], [15]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB2 : ∀ a b : Fin 19, edges patternB.symm 3 2 a b = fastEdge predsB2 a b := by
  have h : checkPairs (fun (a b : Fin 19) => edges patternB.symm 3 2 a b ==
      fastEdge predsB2 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB2 : countSearch (fastEdge predsB2 : Fin 19→Fin 19→Bool) 19 (List.finRange 19) = 2 := by
  decide +kernel

lemma numB2 : packCount patternB 3 2 = 2 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 2 = fastEdge predsB2 by funext a b; exact edgeB2 a b]
  exact execB2

def predsB3 : List (List ℕ) := [[10], [], [15], [13], [1], [2, 18], [3, 16], [4], [5, 21], [6, 19], [7], [8], [9], [0, 10], [11], [12], [3, 13], [14], [15], [6], [17], [18]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB3 : ∀ a b : Fin 22, edges patternB.symm 3 3 a b = fastEdge predsB3 a b := by
  have h : checkPairs (fun (a b : Fin 22) => edges patternB.symm 3 3 a b ==
      fastEdge predsB3 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB3 : countSearch (fastEdge predsB3 : Fin 22→Fin 22→Bool) 22 (List.finRange 22) = 5 := by
  decide +kernel

lemma numB3 : packCount patternB 3 3 = 5 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 3 = fastEdge predsB3 by funext a b; exact edgeB3 a b]
  exact execB3

def predsB4 : List (List ℕ) := [[10], [], [15], [13], [1], [2, 18], [3, 16], [4], [5, 21], [6, 19], [7], [8, 24], [9, 22], [0, 10], [11], [12], [3, 13], [14], [15], [6, 16], [17], [18], [9], [20], [21]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB4 : ∀ a b : Fin 25, edges patternB.symm 3 4 a b = fastEdge predsB4 a b := by
  have h : checkPairs (fun (a b : Fin 25) => edges patternB.symm 3 4 a b ==
      fastEdge predsB4 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB4 : countSearch (fastEdge predsB4 : Fin 25→Fin 25→Bool) 25 (List.finRange 25) = 14 := by
  decide +kernel

lemma numB4 : packCount patternB 3 4 = 14 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 4 = fastEdge predsB4 by funext a b; exact edgeB4 a b]
  exact execB4

def predsB5 : List (List ℕ) := [[10], [], [15], [13], [1], [2, 18], [3, 16], [4], [5, 21], [6, 19], [7], [8, 24], [9, 22], [0, 10], [11, 27], [12, 25], [3, 13], [14], [15], [6, 16], [17], [18], [9, 19], [20], [21], [12], [23], [24]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB5 : ∀ a b : Fin 28, edges patternB.symm 3 5 a b = fastEdge predsB5 a b := by
  have h : checkPairs (fun (a b : Fin 28) => edges patternB.symm 3 5 a b ==
      fastEdge predsB5 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB5 : countSearch (fastEdge predsB5 : Fin 28→Fin 28→Bool) 28 (List.finRange 28) = 42 := by
  decide +kernel

lemma numB5 : packCount patternB 3 5 = 42 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 5 = fastEdge predsB5 by funext a b; exact edgeB5 a b]
  exact execB5

def predsB6 : List (List ℕ) := [[10], [], [15], [13], [1], [2, 18], [3, 16], [4], [5, 21], [6, 19], [7], [8, 24], [9, 22], [0, 10], [11, 27], [12, 25], [3, 13], [14, 30], [15, 28], [6, 16], [17], [18], [9, 19], [20], [21], [12, 22], [23], [24], [15], [26], [27]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edgeB6 : ∀ a b : Fin 31, edges patternB.symm 3 6 a b = fastEdge predsB6 a b := by
  have h : checkPairs (fun (a b : Fin 31) => edges patternB.symm 3 6 a b ==
      fastEdge predsB6 a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma execB6 : countSearch (fastEdge predsB6 : Fin 31→Fin 31→Bool) 31 (List.finRange 31) = 174 := by
  decide +kernel

lemma numB6 : packCount patternB 3 6 = 174 := by
  rw [pack_count_exec]
  rw [show edges patternB.symm 3 6 = fastEdge predsB6 by funext a b; exact edgeB6 a b]
  exact execB6

def Admissible {k : ℕ} (p : Equiv.Perm (Fin k)) (d : ℕ) : Prop :=
  ∀ a b : Fin (k-d),
    p (Fin.castLE (Nat.sub_le _ _) a) < p (Fin.castLE (Nat.sub_le _ _) b) ↔
    p ⟨d+a.val,by have := a.isLt; omega⟩ < p ⟨d+b.val,by have := b.isLt; omega⟩

def admissibleCheck {k : ℕ} (p : Equiv.Perm (Fin k)) (d : ℕ) : Bool :=
  checkPairs fun a b : Fin (k-d) =>
    decide (p (Fin.castLE (Nat.sub_le _ _) a) < p (Fin.castLE (Nat.sub_le _ _) b)) ==
    decide (p ⟨d+a.val,by have := a.isLt; omega⟩ < p ⟨d+b.val,by have := b.isLt; omega⟩)

lemma admissible_of_check {k : ℕ} (p : Equiv.Perm (Fin k)) (d : ℕ)
    (h : admissibleCheck p d = true) : Admissible p d := by
  intro a b
  have he := beq_iff_eq.mp (checkPairs_true h a b)
  simp only [decide_eq_decide] at he
  exact he

lemma admissibleA : Admissible patternA 2 :=
  admissible_of_check _ _ (by decide +kernel)

lemma admissibleB : Admissible patternB 3 :=
  admissible_of_check _ _ (by decide +kernel)

/-- The paper's cutoff assertion across pattern/overlap choices. Counts
    for five positive occurrence numbers are hypothesized to determine all. -/
def FiveCutoff : Prop :=
  ∀ {k l : ℕ} (p : Equiv.Perm (Fin k)) (q : Equiv.Perm (Fin l))
    (d e : ℕ), 2≤d → d<k → 2≤e → e<l →
    Admissible p d → Admissible q e →
    (∀ j, 1≤j → j≤5 → packCount p d j = packCount q e j) →
    ∀ j, 1≤j → packCount p d j = packCount q e j

theorem exact_five_cutoff_refuted : ¬ FiveCutoff := by
  intro h
  have eq := h patternA patternB 2 3 (by decide) (by decide) (by decide) (by decide) admissibleA admissibleB (by
    intro j h1 h5
    interval_cases j
    · rw [numA1,numB1]
    · rw [numA2,numB2]
    · rw [numA3,numB3]
    · rw [numA4,numB4]
    · rw [numA5,numB5]) 6 (by decide)
  rw [numA6,numB6] at eq
  norm_num at eq

#print axioms exact_five_cutoff_refuted
end CoverCutoff

