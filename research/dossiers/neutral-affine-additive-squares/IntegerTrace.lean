import ScalarTrace
import Mathlib.Data.Int.Interval

namespace IntegerTrace

theorem cast_eval (a x : ℤ) (cs : List ℤ) :
    (ScalarTrace.zeval a x cs : ℝ) =
      ScalarTrace.eval a x (cs.map fun c : ℤ => (c : ℝ)) := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    simpa [ScalarTrace.zeval,ScalarTrace.eval,Int.cast_add,Int.cast_mul] using ih (a*x+c)

def box (B : ℤ) : Finset ℤ := Finset.Icc (-B) B

theorem box_iff (B n : ℤ) : n ∈ box B ↔ |n| ≤ B := by
  rw [abs_le]
  exact Finset.mem_Icc

theorem can_clip (a B C : ℤ) (apos : 1 < |a|) (Bpos : 0 ≤ B)
    (hsafe : C ≤ (|a|-1)*B) (cs ds : List ℤ) (hC : ∀ e ∈ ds, |e| ≤ C)
    (hend : ScalarTrace.zeval a 0 (cs++ds)=0) :
    ScalarTrace.zeval a 0 cs ∈ box B := by
  rw [box_iff]
  have hh : |(a : ℝ)| > 1 := by exact_mod_cast apos
  have hhB : (C : ℝ) ≤ (|(a : ℝ)|-1)*B := by exact_mod_cast hsafe
  have hpos : (0 : ℝ) ≤ B := by exact_mod_cast Bpos
  let u := cs.map fun e : ℤ => (e : ℝ)
  let v := ds.map fun e : ℤ => (e : ℝ)
  have hu : ∀ e ∈ v, |e| ≤ (C : ℝ) := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact_mod_cast hC i hi
  have hfin : ScalarTrace.eval a 0 (u++v)=0 := by
    have h := cast_eval a 0 (cs++ds)
    simpa [hend,u,v] using h.symm
  have h := ScalarTrace.prefixes_back (a : ℝ) B C hh hhB u v hu hfin hpos
  have f := cast_eval a 0 cs
  rw [Int.cast_zero] at f
  change |ScalarTrace.eval (a : ℝ) 0 (cs.map fun e : ℤ => (e : ℝ))| ≤ (B : ℝ) at h
  rw [← f] at h
  exact_mod_cast h

theorem next_checked (a x c B : ℤ) :
    (a*x+c) ∈ box B ↔ -(B:ℤ) ≤ a*x+c ∧ a*x+c ≤ B := by
  exact Finset.mem_Icc

end IntegerTrace

#print axioms IntegerTrace.can_clip
