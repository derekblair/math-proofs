import Mathlib.Data.List.Sort

namespace HaarKernelSort

def place (x : ℕ) (xs : List ℕ) (tailMerge : List ℕ → List ℕ) : List ℕ → List ℕ
  | [] => x::xs
  | y::ys => if x.ble y then x :: tailMerge (y::ys) else y::place x xs tailMerge ys

def merge : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x::xs, ys => place x xs (merge xs) ys
termination_by structural xs ys => xs

theorem merge_nil (xs : List ℕ) : merge xs [] = xs := by cases xs <;> rfl

theorem merge_cons (x y : ℕ) (xs ys : List ℕ) :
    merge (x::xs) (y::ys) =
      if x.ble y then x::merge xs (y::ys) else y::merge (x::xs) ys := rfl

theorem perm_merge (xs ys : List ℕ) : (merge xs ys).Perm (xs++ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    induction ys with
    | nil => rw [merge_nil, List.append_nil]
    | cons y ys iy =>
      rw [merge_cons]
      split
      · exact (ih (y::ys)).cons x
      · exact (iy.cons y).trans (List.perm_middle.symm)

def round : List (List ℕ) → List (List ℕ)
  | a::b::r => merge a b :: round r
  | r => r

theorem perm_round (r : List (List ℕ)) : (round r).flatten.Perm r.flatten := by
  match r with
  | [] | [_] => exact List.Perm.refl _
  | a::b::r =>
    simp only [round, List.flatten_cons]
    rw [← List.append_assoc]
    exact (perm_merge a b).append (perm_round r)

def run : ℕ → List (List ℕ) → List ℕ
  | 0,r => r.flatten
  | n+1,r => run n (round r)

theorem perm_run (n : ℕ) (r : List (List ℕ)) : (run n r).Perm r.flatten := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => exact (ih (round r)).trans (perm_round r)

def sort (n : ℕ) (l : List ℕ) : List ℕ := run n (l.map (fun x => [x]))

theorem perm_sort (n : ℕ) (l : List ℕ) : (sort n l).Perm l := by
  unfold sort
  have e : (l.map fun x => [x]).flatten=l := by induction l <;> simp_all
  exact (perm_run n _).trans (List.Perm.of_eq e)

end HaarKernelSort
