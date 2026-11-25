import sys
A=[0,2,1,3]
B=[4,0,11,6,1,12,7,2,13,8,3,14,9,5,15,10]
cs=[[1,2,5,14,42,132],[1,2,5,14,42,174]]
fmt=lambda a:'['+', '.join(map(str,a))+']'
with open('Examples.lean','w') as out:
 def W(x): print(x,file=out)
 W('''import Pack

namespace CoverCutoff

def fastEdge {n : ℕ} (preds : List (List ℕ)) (a b : Fin n) : Bool :=
  (preds[b.val]?.getD []).contains a.val

def checkPairs {n : ℕ} (p : Fin n→Fin n→Bool) : Bool :=
  (List.finRange n).all fun a => (List.finRange n).all (p a)

lemma checkPairs_true {n : ℕ} {p : Fin n→Fin n→Bool} (h : checkPairs p = true) (a b : Fin n) :
    p a b = true := by
  have h1 := List.all_eq_true.mp h a (List.mem_finRange a)
  exact List.all_eq_true.mp h1 b (List.mem_finRange b)
''')
 for name,p,step,expected in zip('AB',[A,B],[2,3],cs):
  k=len(p);inv=sorted(range(k),key=lambda i:p[i])
  W(f'''def pattern{name} : Equiv.Perm (Fin {k}) where
  toFun := !{fmt(p)}
  invFun := !{fmt(inv)}
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide
''')
  for j,val in enumerate(expected,1):
   n=k+(j-1)*step
   D=[set() for _ in range(n)]
   for t in range(j):
    for a,b in zip(inv,inv[1:]): D[t*step+b].add(t*step+a)
   po='['+', '.join(fmt(sorted(x)) for x in D)+']'
   W(f'''def preds{name}{j} : List (List ℕ) := {po}

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
lemma edge{name}{j} : ∀ a b : Fin {n}, edges pattern{name}.symm {step} {j} a b = fastEdge preds{name}{j} a b := by
  have h : checkPairs (fun (a b : Fin {n}) => edges pattern{name}.symm {step} {j} a b ==
      fastEdge preds{name}{j} a b) = true := by decide +kernel
  intro a b
  exact beq_iff_eq.mp (checkPairs_true h a b)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
lemma exec{name}{j} : countSearch (fastEdge preds{name}{j} : Fin {n}→Fin {n}→Bool) {n} (List.finRange {n}) = {val} := by
  decide +kernel

lemma num{name}{j} : packCount pattern{name} {step} {j} = {val} := by
  rw [pack_count_exec]
  rw [show edges pattern{name}.symm {step} {j} = fastEdge preds{name}{j} by funext a b; exact edge{name}{j} a b]
  exact exec{name}{j}
''')
 W('''def Admissible {k : ℕ} (p : Equiv.Perm (Fin k)) (d : ℕ) : Prop :=
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
''')
