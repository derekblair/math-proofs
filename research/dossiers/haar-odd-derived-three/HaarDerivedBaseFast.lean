import HaarDerivedGirth22
import HaarDerivedFastSort
namespace HaarDerivedGirth22
open HaarSharpPortGeometry
open HaarSharpLamp (Row words scan compatible compat_members scan_good)
def keyLE (a b : Row) : Bool := decide (a.k≤b.k)
def sortedFast (n : ℕ) : List Row :=
  HaarDerivedFastSort.sortF keyLE 11 ((words n none).map row)
theorem cert_fast {n : ℕ} (hlen : (words n none).length≤2^11)
    (good : scan (sortedFast n) = true) {u v : List (Fin 3)}
    (hu : u ∈ words n none) (hv : v ∈ words n none)
    (he : value port true u = value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  obtain ⟨S,P⟩ := HaarDerivedFastSort.sorted_perm keyLE
    (fun a b c ab bc => by simp only [keyLE,decide_eq_true_eq] at *; exact Nat.le_trans ab bc)
    (fun a b => by simp only [Bool.or_eq_true,keyLE,decide_eq_true_eq]; exact Nat.le_total _ _)
    11 ((words n none).map row) (by simpa using hlen)
  have sorted : (sortedFast n).Pairwise (fun a b => a.k ≤ b.k) := by
    simpa only [sortedFast,keyLE,decide_eq_true_eq] using S
  have mem (w : List (Fin 3)) (hw : w ∈ words n none) : row w ∈ sortedFast n :=
    P.mem_iff.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have c := compat_members (scan_good _ good sorted) (mem _ hu) (mem _ hv)
  simpa [compatible,row,he] using c
end HaarDerivedGirth22
#print axioms HaarDerivedGirth22.cert_fast
