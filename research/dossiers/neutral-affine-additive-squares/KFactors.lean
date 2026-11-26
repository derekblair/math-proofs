import KCut

namespace KFactors
open KCut CutLift AffineAddress

def flatPref {n : ℕ} (B : Fin n → List ℤ) (i : Fin (n+1)) : List ℤ :=
  ((List.ofFn B).take i.val).flatten

theorem flatPref_step {n : ℕ} (B : Fin n → List ℤ) (j : Fin n) :
    flatPref B j.succ = flatPref B j.castSucc ++ B j := by
  have lt : j.val < (List.ofFn B).length := by simp
  unfold flatPref
  change ((List.ofFn B).take (j.val+1)).flatten = _
  rw [List.take_succ_eq_append_getElem lt, List.flatten_append, List.getElem_ofFn]
  simp

theorem chain_concat {n : ℕ} (P : Fin (n+1) → List ℤ) (B : Fin n → List ℤ)
    (h : ∀ j : Fin n, P j.succ = P j.castSucc ++ B j) (i : Fin (n+1)) :
    P i = P 0 ++ flatPref B i := by
  induction i using Fin.induction with
  | zero => simp [flatPref]
  | succ j ih => rw [h j, ih, flatPref_step, List.append_assoc]

theorem all_equal {n : ℕ} (F : Fin (n+1) → ℤ × ℤ)
    (h : ∀ j : Fin n, F j.succ = F j.castSucc) (i : Fin (n+1)) :
    F i = F 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => exact (h j).trans ih

def Actual (w : List ℤ) (k : ℕ) : Prop :=
  ∃ (u r : List ℤ) (B : Fin (k+1) → List ℤ),
    w = u ++ (List.ofFn B).flatten ++ r ∧ r ≠ [] ∧
    (∀ j, 0 < (B j).length) ∧ (∀ j, σ (B j) = σ (B 0))

theorem chain_to_actual {w : List ℤ} {k : ℕ} (T : Chain w (k+1)) (h : strict T)
    (z : ∀ j, gaps T j = 0) : Actual w k := by
  classical
  choose B eq sig using fun i => block_real T i (fun j => (h j).le)
  let L := T (Fin.last (k+1))
  have hd := chain_concat (fun i => (T i).head) B eq (Fin.last (k+1))
  have hf : L.head = (T 0).head ++ (List.ofFn B).flatten := by
    change L.head = _ at hd
    unfold flatPref at hd
    rw [List.take_of_length_le (by rw [List.length_ofFn]; exact Nat.le_refl _)] at hd
    exact hd
  refine ⟨(T 0).head,L.letter::L.tail,B,?_,by simp,?_,?_⟩
  · exact L.decomp.trans (by rw [hf])
  · intro j
    have ht := h j
    change (T j.castSucc).head.length < (T j.succ).head.length at ht
    rw [eq j,List.length_append] at ht
    omega
  · have ez : ∀ j : Fin k, block T j.succ = block T j.castSucc :=
      fun j => sub_eq_zero.mp (z j)
    intro j
    exact (sig j).symm.trans ((all_equal (block T) ez j).trans (sig 0))

theorem of_actual {w : List ℤ} {k : ℕ} (h : Actual w k) :
    ∃ T : Chain w (k+1), strict T ∧ ∀ j, gaps T j = 0 := by
  classical
  obtain ⟨u,r,B,e,ne,pos,same⟩ := h
  have pref : ∀ i : Fin (k+1+1), ∃ C : Cut w, C.head = u ++ flatPref B i := by
    intro i
    let tail := ((List.ofFn B).drop i.val).flatten ++ r
    have et : w = (u ++ flatPref B i) ++ tail := by
      unfold tail flatPref
      rw [e, List.append_assoc, List.append_assoc, ← List.append_assoc
        ((List.ofFn B).take i.val).flatten ((List.ofFn B).drop i.val).flatten r,
        ← List.flatten_append,List.take_append_drop]
    have nt : tail ≠ [] := by simp [tail,ne]
    cases ht : tail with
    | nil => exact (nt ht).elim
    | cons x xs => exact ⟨⟨u ++ flatPref B i,x,xs,by simpa [ht] using et⟩,rfl⟩
  choose T eq using pref
  have eqstep (j : Fin (k+1)) :
      (T j.succ).head = (T j.castSucc).head ++ B j := by
    rw [eq,eq,flatPref_step,List.append_assoc]
  refine ⟨T,?_ ,?_⟩
  · intro j
    have hp := pos j
    unfold idx
    rw [eqstep,List.length_append]; omega
  · have sig (j : Fin (k+1)) : block T j = σ (B j) := by
      rw [block,eqstep,sig_append]
      abel
    intro j
    rw [gaps,sig,sig,same j.succ,same j.castSucc,sub_self]

end KFactors

#print axioms KFactors.chain_to_actual
#print axioms KFactors.of_actual
