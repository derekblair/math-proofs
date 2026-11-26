import HaarSharpLamp
namespace HaarDerivedFastSort
variable {α : Type*} (le : α → α → Bool)

def mergeF : ℕ → List α → List α → List α
  | 0, xs, ys => xs++ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x::mergeF n xs (y::ys) else y::mergeF n (x::xs) ys

theorem merge_eq (n : ℕ) (xs ys : List α) (h : xs.length+ys.length≤n) :
    mergeF le n xs ys=List.merge xs ys le := by
  induction n generalizing xs ys with
  | zero =>
    have a : xs.length=0 := by omega
    have b : ys.length=0 := by omega
    rw [List.length_eq_zero_iff.mp a,List.length_eq_zero_iff.mp b]
    simp [mergeF]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeF]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeF]
      | cons y ys =>
        simp only [mergeF,List.merge]
        split <;> congr 1 <;> apply ih <;> simp at h ⊢ <;> omega

def sortF : ℕ → List α → List α
  | 0, xs => xs
  | n+1, xs =>
    let m := xs.length/2
    mergeF le xs.length (sortF n (xs.take m)) (sortF n (xs.drop m))

theorem sorted_perm (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a)
    (n : ℕ) (xs : List α) (h : xs.length ≤ 2^n) :
    (sortF le n xs).Pairwise (fun a b => le a b = true) ∧ (sortF le n xs).Perm xs := by
  induction n generalizing xs with
  | zero =>
    constructor
    · cases xs with
      | nil => simp [sortF]
      | cons a as =>
        have len : as.length=0 := by simp only [pow_zero,List.length_cons] at h;omega
        rw [List.length_eq_zero_iff.mp len]
        simp [sortF]
    · exact List.Perm.refl _
  | succ n ih =>
    let m := xs.length/2
    have a : (xs.take m).length≤2^n := by
      rw [pow_succ] at h
      simp [m]
      omega
    have b : (xs.drop m).length≤2^n := by
      rw [pow_succ] at h
      simp [m]
      omega
    obtain ⟨aS,aP⟩ := ih (xs.take m) a
    obtain ⟨bS,bP⟩ := ih (xs.drop m) b
    have bound : (sortF le n (xs.take m)).length + (sortF le n (xs.drop m)).length ≤ xs.length := by
      rw [aP.length_eq,bP.length_eq]
      have hh := congrArg List.length (List.take_append_drop m xs)
      simpa only [List.length_append] using hh.le
    change (mergeF le xs.length (sortF le n (xs.take m)) (sortF le n (xs.drop m))).Pairwise (fun a b => le a b = true) ∧ (mergeF le xs.length (sortF le n (xs.take m)) (sortF le n (xs.drop m))).Perm xs
    rw [merge_eq le _ _ _ bound]
    constructor
    · exact List.pairwise_merge trans total _ _ aS bS
    · change (List.merge (sortF le n (xs.take m)) (sortF le n (xs.drop m)) le).Perm xs
      exact (List.merge_perm_append (le:=le)).trans ((aP.append bP).trans (List.Perm.of_eq (List.take_append_drop m xs)))

end HaarDerivedFastSort
#print axioms HaarDerivedFastSort.sorted_perm
