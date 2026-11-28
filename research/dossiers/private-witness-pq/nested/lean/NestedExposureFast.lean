import NestedExposureCore

namespace NestedExposure
def fastScan (accept : Moments → Bool) : Nat → Nat → Nat → Moments → Bool
  | 0, rest, _, m => if rest=0 then accept m else true
  | k+1, rest, lower, m =>
    let left := max lower (rest-13*k)
    let right := min 13 (rest/(k+1))
    (List.range (right+1-left)).all (fun i =>
      let a := left+i
      fastScan accept k (rest-a) a (advance m a))

private theorem local_bounds (l : List Nat) (a : Nat)
    (lower : ∀ p∈l, a≤p) (upper : ∀ p∈l, p≤13) :
    a*l.length≤l.sum ∧ l.sum≤13*l.length := by
  induction l with
  | nil => simp
  | cons v r ih =>
    have b := ih (fun x hx => lower x (List.mem_cons_of_mem _ hx))
      (fun x hx => upper x (List.mem_cons_of_mem _ hx))
    have x := lower v (by simp)
    have y := upper v (by simp)
    simp only [List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

/-- Exact soundness of the bounded-search generator. It enumerates only
children whose remaining sum can be attained with future sorted values. -/
theorem fast_scan_sound (accept : Moments→Bool) (l : List Nat) (lo : Nat) (m : Moments)
    (inc : l.Pairwise (·≤·)) (lower : ∀ x∈l, lo≤x) (upper : ∀ x∈l, x≤13)
    (h : fastScan accept l.length l.sum lo m=true) :
    accept (l.foldl advance m)=true := by
  induction l generalizing lo m with
  | nil => simpa [fastScan] using h
  | cons x l ih =>
    obtain ⟨xl,inc'⟩ := List.pairwise_cons.mp inc
    have up' : ∀ v∈l, v≤13 := fun v hv=>upper v (List.mem_cons_of_mem _ hv)
    have b := local_bounds l x xl up'
    let L := max lo (x+l.sum-13*l.length)
    let R := min 13 ((x+l.sum)/(l.length+1))
    have lo' : L≤x := max_le_iff.mpr ⟨lower x (by simp),by omega⟩
    have hi : x≤R := le_min (upper x (by simp))
      ((Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_succ]; omega))
    have h' : (List.range (R+1-L)).all (fun i =>
        fastScan accept l.length (x+l.sum-(L+i)) (L+i) (advance m (L+i)))=true := by
      simpa only [List.length_cons,List.sum_cons,fastScan] using h
    have m' : x-L ∈ List.range (R+1-L) := List.mem_range.mpr (by omega)
    have ha := List.all_eq_true.mp h' (x-L) m'
    rw [Nat.add_sub_of_le lo'] at ha
    rw [show x+l.sum-x=l.sum by omega] at ha
    exact ih x (advance m x) inc' xl up' ha

#print axioms fast_scan_sound
end NestedExposure
