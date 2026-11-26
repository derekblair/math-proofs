import HaarMatrix31PackedSound
import HaarMatrix31WordsBridge
import HaarMatrix31PackedCheck
import HaarKernelSort

namespace HaarMatrix31NoShort
open HaarAllNoncommuting HaarMatrix31Core HaarMatrix31PackedSound
open HaarMatrix31WordsBridge HaarMatrix31Packed

noncomputable def algebraStep (pos : Bool) (j : Fin 3) (g : UT) : UT :=
  g * (if pos then HaarHalfCollision.port x y j else (HaarHalfCollision.port x y j)⁻¹)

theorem link (L : List (Fin 3)) : project (value (HaarHalfCollision.prodFrom x y 0 L)) =
    run (fun p j s => move p j.val s) zero true L := by
  have h := run_natural algebraStep (fun p j s => move p j.val s)
    (fun g => project (value g)) project_step (1 : UT) true L
  rw [project_one] at h
  have e := run_signed_mul x y (1 : UT) 0 L
  change run algebraStep 1 true L = _ at e
  rw [one_mul] at e
  simpa only [e] using h

theorem excluded (k : ℕ) (hk : 2 ≤ k) (nd : (words zero true 3 k).Nodup) :
    ¬ HasCycle x y (2*k) := by
  intro hc
  obtain ⟨L,R,hl,hr,gl,gr,ne,eq⟩ := HaarHalfCollision.exists_collision x y k hk hc
  apply ne
  apply injective_keys k nd L R hl hr gl gr
  rw [← link L, ← link R, eq]

theorem fromChecker (k : ℕ) (hk : 2 ≤ k) (h : strict (HaarKernelSort.sort (k+1) (words zero true 3 k)) = true) :
    ¬ HasCycle x y (2*k) := by
  apply excluded k hk
  have nd := (HaarMatrix31PackedCheck.checker_sound _ h).imp (fun lt => Nat.ne_of_lt lt)
  exact (HaarKernelSort.perm_sort _ _).nodup_iff.mp nd

end HaarMatrix31NoShort
#print axioms HaarMatrix31NoShort.excluded
