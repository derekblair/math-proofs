import HaarClass6ParallelSeparationCore

namespace HaarClass6ParallelPairs
open HaarClass6ParallelWords HaarClass6ParallelSeparationCore HaarClass3Separation64

def good (I J : Fin 64) : Prop :=
  let p := rowW I.val
  let q := rowW J.val
  I=J ∨ I.val%2≠J.val%2 ∨ small3 (i p-i q) ∨ small3 (j p-j q) ∨
  (i p=i q ∧ j p=j q ∧ small3 (k p-k q)) ∨
  (i p=i q ∧ j p=j q ∧ k p=k q ∧ a p=a q ∧ small3 (b q-b p))

instance (I J : Fin 64) : Decidable (good I J) := by unfold good; infer_instance

set_option maxRecDepth 22000
set_option maxHeartbeats 0

private theorem p0 : ∀ (u : Fin 8) (v : Fin 64), good ⟨0+u.val,by omega⟩ v := by
  decide +kernel

private theorem p1 : ∀ (u : Fin 8) (v : Fin 64), good ⟨8+u.val,by omega⟩ v := by
  decide +kernel

private theorem p2 : ∀ (u : Fin 8) (v : Fin 64), good ⟨16+u.val,by omega⟩ v := by
  decide +kernel

private theorem p3 : ∀ (u : Fin 8) (v : Fin 64), good ⟨24+u.val,by omega⟩ v := by
  decide +kernel

private theorem p4 : ∀ (u : Fin 8) (v : Fin 64), good ⟨32+u.val,by omega⟩ v := by
  decide +kernel

private theorem p5 : ∀ (u : Fin 8) (v : Fin 64), good ⟨40+u.val,by omega⟩ v := by
  decide +kernel

private theorem p6 : ∀ (u : Fin 8) (v : Fin 64), good ⟨48+u.val,by omega⟩ v := by
  decide +kernel

private theorem p7 : ∀ (u : Fin 8) (v : Fin 64), good ⟨56+u.val,by omega⟩ v := by
  decide +kernel

theorem all_pairs (i j : Fin 64) : good i j := by
  by_cases q0 : i.val<8
  · have e := p0 ⟨i.val-0,by omega⟩ j
    exact (show (⟨0+(i.val-0),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
  · by_cases q1 : i.val<16
    · have e := p1 ⟨i.val-8,by omega⟩ j
      exact (show (⟨8+(i.val-8),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
    · by_cases q2 : i.val<24
      · have e := p2 ⟨i.val-16,by omega⟩ j
        exact (show (⟨16+(i.val-16),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
      · by_cases q3 : i.val<32
        · have e := p3 ⟨i.val-24,by omega⟩ j
          exact (show (⟨24+(i.val-24),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
        · by_cases q4 : i.val<40
          · have e := p4 ⟨i.val-32,by omega⟩ j
            exact (show (⟨32+(i.val-32),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
          · by_cases q5 : i.val<48
            · have e := p5 ⟨i.val-40,by omega⟩ j
              exact (show (⟨40+(i.val-40),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
            · by_cases q6 : i.val<56
              · have e := p6 ⟨i.val-48,by omega⟩ j
                exact (show (⟨48+(i.val-48),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e
              · have e := p7 ⟨i.val-56,by omega⟩ j
                exact (show (⟨56+(i.val-56),by omega⟩ : Fin 64)=i from Fin.ext (by dsimp; omega)) ▸ e

end HaarClass6ParallelPairs
#print axioms HaarClass6ParallelPairs.all_pairs
