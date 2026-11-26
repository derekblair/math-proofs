import RibbonAllOddSlopeFinalCore
namespace RibbonAllOddField
open RibbonStationaryField (Branch branch)

def Verified (B : Branch) : Prop :=
  ∃ C : Cover, RowValid B.p C ∧ GeomValid B C ∧
    ∀ k : Fin C.rows.size, ∃ p : PrimeCert, primeValid B C.rows[k] p

def Chunk (start size : Nat) : Prop := ∀ k : Fin size, Verified (branch (start+k.val))

theorem stitch (P0 : Chunk 0 8) (P1 : Chunk 8 8) (P2 : Chunk 16 8) (P3 : Chunk 24 8) (P4 : Chunk 32 8) (P5 : Chunk 40 8) (P6 : Chunk 48 8) (P7 : Chunk 56 8) (P8 : Chunk 64 8) (P9 : Chunk 72 4) (r : Fin 76) : Verified (branch r.val) := by
  let a := r.val/8
  let b := r.val%8
  have qa : a≤9 := by have := r.isLt; dsimp [a]; omega
  have qb : b<8 := by dsimp [b]; omega
  have e : r.val=8*a+b := by dsimp [a,b]; omega
  interval_cases h : a
  · have eq : r.val=0+b := by simpa [h] using e
    rw [eq]
    exact P0 ⟨b,qb⟩
  · have eq : r.val=8+b := by simpa [h] using e
    rw [eq]
    exact P1 ⟨b,qb⟩
  · have eq : r.val=16+b := by simpa [h] using e
    rw [eq]
    exact P2 ⟨b,qb⟩
  · have eq : r.val=24+b := by simpa [h] using e
    rw [eq]
    exact P3 ⟨b,qb⟩
  · have eq : r.val=32+b := by simpa [h] using e
    rw [eq]
    exact P4 ⟨b,qb⟩
  · have eq : r.val=40+b := by simpa [h] using e
    rw [eq]
    exact P5 ⟨b,qb⟩
  · have eq : r.val=48+b := by simpa [h] using e
    rw [eq]
    exact P6 ⟨b,qb⟩
  · have eq : r.val=56+b := by simpa [h] using e
    rw [eq]
    exact P7 ⟨b,qb⟩
  · have eq : r.val=64+b := by simpa [h] using e
    rw [eq]
    exact P8 ⟨b,qb⟩
  · have eq : r.val=72+b := by simpa [h] using e
    have qb : b<4 := by have := r.isLt; omega
    rw [eq]
    exact P9 ⟨b,qb⟩

end RibbonAllOddField
#print axioms RibbonAllOddField.stitch
