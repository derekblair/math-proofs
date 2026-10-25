import Mathproofs.ESIdentity
import Mathproofs.ESCovering

/-!
# The six identity subclasses modulo 9240

The exact CRT table and its one-out-of-eleven residue count are proved here.
This is a count of residue subclasses, not a prime-density or novelty theorem.
-/

namespace ESIdentityCRT

def hardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}
def coveredClasses : Finset ℕ := {8401, 1801, 1009, 3649, 7081, 8929}

theorem covered_classes_exact (n : ℕ) :
    n % 840 ∈ hardClasses ∧ n % 264 = 217 ↔ n % 9240 ∈ coveredClasses := by
  simp only [hardClasses, coveredClasses, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Each parent class has eleven sub-progressions modulo 9240. -/
theorem parent_fiber_card (r : ℕ) (hr : r < 840) :
    ((Finset.range 9240).filter (fun n => n % 840 = r)).card = 11 := by
  have he : ((Finset.range 9240).filter (fun n => n % 840 = r)) =
      (Finset.range 11).image (fun j => r + 840 * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hn, he⟩
      exact ⟨n / 840, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      constructor <;> omega
  rw [he, Finset.card_image_of_injective]
  · simp
  · intro a b he
    dsimp at he
    omega

/-- Exactly one of each parent's eleven residue subclasses satisfies the identity. -/
theorem covered_parent_fiber_card (r : ℕ) (hr : r ∈ hardClasses) :
    ((Finset.range 9240).filter (fun n => n % 840 = r ∧ n % 264 = 217)).card = 1 := by
  have he : ((Finset.range 9240).filter (fun n => n % 840 = r ∧ n % 264 = 217)) =
      coveredClasses.filter (fun n => n % 840 = r) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    have hlt : n ∈ coveredClasses → n < 9240 := by
      simp only [coveredClasses, Finset.mem_insert, Finset.mem_singleton]
      omega
    constructor
    · rintro ⟨hn, he, hc⟩
      refine ⟨?_,he⟩
      have hx := (covered_classes_exact n).mp ⟨he ▸ hr,hc⟩
      simpa [Nat.mod_eq_of_lt hn] using hx
    · rintro ⟨hn,he⟩
      have hh := (covered_classes_exact n).mpr (by simpa [Nat.mod_eq_of_lt (hlt hn)] using hn)
      exact ⟨hlt hn,he,hh.2⟩
  rw [he]
  simp only [hardClasses, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every member of a listed subclass has positive natural covering witnesses. -/
theorem covered_class_identity (n : ℕ) (hn : n % 9240 ∈ coveredClasses) :
    ESCovering.Covered n := by
  obtain ⟨x, y, z, hx, hy, hz, _, _, _, hid⟩ :=
    es_covering_217mod264 n ((covered_classes_exact n).mpr hn).2
  exact ⟨x, y, z, hx, hy, hz, hid⟩

end ESIdentityCRT
