import HaarDerivedTrie

namespace HaarDerivedGirth22
open HaarSharpLamp (words Row compatible compat_members)
open HaarSharpPortGeometry
def keys10 : List Nat := ((words 10 none).map row).map Row.k

def portions (step : ℕ) : ℕ → List Nat → List (List Nat)
  | 0, _ => []
  | n+1, xs => xs.take step :: portions step n (xs.drop step)

theorem portion_count (s k : ℕ) (xs : List Nat) : (portions s k xs).length=k := by
  induction k generalizing xs with | zero => rfl | succ k ih => simp [portions, ih]

theorem portion_get (s k : ℕ) (xs : List Nat) (i : ℕ) (hi : i<(portions s k xs).length) :
    (portions s k xs)[i] = (xs.drop (i*s)).take s := by
  induction k generalizing xs i with
  | zero => simp [portions] at hi
  | succ k ih =>
    cases i with
    | zero => simp [portions]
    | succ i =>
      have r : i < (portions s k (xs.drop s)).length := by
        rw [portion_count] at hi ⊢
        omega
      change (portions s k (xs.drop s))[i]'r=(xs.drop ((i+1)*s)).take s
      rw [ih (xs.drop s) i r,List.drop_drop,Nat.succ_mul,Nat.add_comm s (i*s)]

theorem portion_flat (s k : ℕ) (xs : List Nat) (size : xs.length≤k*s) :
    (portions s k xs).flatten=xs := by
  induction k generalizing xs with
  | zero =>
    simp only [Nat.zero_mul, Nat.le_zero] at size
    rw [List.length_eq_zero_iff.mp size]
    rfl
  | succ k ih =>
    simp only [portions,List.flatten_cons]
    rw [ih]
    · exact List.take_append_drop _ _
    · rw [List.length_drop]
      rw [Nat.succ_mul] at size
      omega

theorem cert_explicit {I : List Nat} (ids : keys10=I) (nd : I.Nodup) {u v : List (Fin 3)}
    (hu : u ∈ words 10 none) (hv : v ∈ words 10 none)
    (he : value port true u = value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  rw [←ids,keys10,List.Nodup,List.pairwise_map] at nd
  have comp : ((words 10 none).map row).Pairwise compatible := by
    exact nd.imp (fun h => Or.inl h)
  have c := compat_members comp (List.mem_map.mpr ⟨u,hu,rfl⟩) (List.mem_map.mpr ⟨v,hv,rfl⟩)
  simpa [compatible,row,he] using c

end HaarDerivedGirth22
