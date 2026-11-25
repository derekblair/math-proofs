import GapBallot

namespace CoverCutoff
open Finset FussCover

variable {h : ℕ} (S : BallotSet h)

def ballotUp (i : Fin h) : Fin (2*h) := S.val.orderEmbOfFin S.prop.1 i
def ballotDown (i : Fin h) : Fin (2*h) :=
  (S.valᶜ : Finset _).orderEmbOfFin (comp_card S.val S.prop.1) i

lemma ballotUp_mem (i : Fin h) : ballotUp S i ∈ S.val := S.val.orderEmbOfFin_mem _ i
lemma ballotDown_not_mem (i : Fin h) : ballotDown S i ∉ S.val :=
  Finset.mem_compl.mp ((S.valᶜ : Finset _).orderEmbOfFin_mem _ i)

lemma ballotUp_mono : StrictMono (ballotUp S) := (S.val.orderEmbOfFin S.prop.1).strictMono
lemma ballotDown_mono : StrictMono (ballotDown S) :=
  ((S.valᶜ : Finset _).orderEmbOfFin (comp_card S.val S.prop.1)).strictMono
lemma ballot_cross (i : Fin h) : ballotUp S i < ballotDown S i :=
  ((ballot_iff_orders S.val S.prop.1).mp S.prop.2) i

def restoreU (i : ℕ) : ℕ :=
  if low : i < 2 then i else if hi : i < h+2 then 3+(ballotUp S ⟨i-2,by omega⟩).val else 0
def restoreV (i : ℕ) : ℕ :=
  if iz : i = 0 then 2 else if hi : i < h+1 then 3+(ballotDown S ⟨i-1,by omega⟩).val else 2*h+3

@[simp] lemma restoreU_zero : restoreU S 0 = 0 := by simp [restoreU]
@[simp] lemma restoreU_one : restoreU S 1 = 1 := by simp [restoreU]
@[simp] lemma restoreV_zero : restoreV S 0 = 2 := by simp [restoreV]
@[simp] lemma restoreV_last : restoreV S (h+1)=2*h+3 := by simp [restoreV]

lemma restoreU_other (i : ℕ) (ilow : 2 ≤ i) (hi : i < h+2) :
    restoreU S i = 3+(ballotUp S ⟨i-2,by omega⟩).val := by
  unfold restoreU
  rw [dif_neg (show ¬ i < 2 by omega),dif_pos hi]

lemma restoreV_other (i : ℕ) (ilow : 1 ≤ i) (hi : i < h+1) :
    restoreV S i = 3+(ballotDown S ⟨i-1,by omega⟩).val := by
  unfold restoreV
  rw [dif_neg (show i ≠ 0 by omega),dif_pos hi]

lemma restoreU_lt (i : ℕ) (hi : i < h+2) : restoreU S i < 2*h+4 := by
  by_cases ilow : 2 ≤ i
  · rw [restoreU_other S i ilow hi]
    have := (ballotUp S ⟨i-2,by omega⟩).isLt
    omega
  · rw [restoreU, dif_pos (show i < 2 by omega)]
    omega

lemma restoreV_lt (i : ℕ) (hi : i < h+2) : restoreV S i < 2*h+4 := by
  by_cases h0 : i = 0
  · subst i; simp [restoreV] <;> omega
  by_cases hl : i = h+1
  · subst i; simp [restoreV] <;> omega
  rw [restoreV_other S i (by omega) (by omega)]
  have := (ballotDown S ⟨i-1,by omega⟩).isLt
  omega

lemma restoreU_strict (i j : ℕ) (ij : i < j) (hj : j < h+2) :
    restoreU S i < restoreU S j := by
  by_cases ilow : 2 ≤ i
  · rw [restoreU_other S i ilow (by omega),restoreU_other S j (by omega) hj]
    have k := ballotUp_mono S (show (⟨i-2,by omega⟩ : Fin h)<⟨j-2,by omega⟩ from by
      change i-2 < j-2; omega)
    change (ballotUp S ⟨i-2,by omega⟩).val < (ballotUp S ⟨j-2,by omega⟩).val at k
    omega
  · rw [restoreU,dif_pos (show i < 2 by omega)]
    by_cases jl : 2 ≤ j
    · rw [restoreU_other S j jl hj]; omega
    · rw [restoreU,dif_pos (show j < 2 by omega)]; omega

lemma restoreV_strict (i j : ℕ) (ij : i < j) (hj : j < h+2) :
    restoreV S i < restoreV S j := by
  by_cases jlast : j = h+1
  · subst j
    rw [restoreV_last]
    rcases Nat.eq_zero_or_pos i with rfl|ip
    · simp <;> omega
    · rw [restoreV_other S i ip ij]
      have := (ballotDown S ⟨i-1,by omega⟩).isLt
      omega
  · rw [restoreV_other S j (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos i with rfl|ip
    · simp <;> omega
    · rw [restoreV_other S i ip (by omega)]
      have k := ballotDown_mono S (show (⟨i-1,by omega⟩ : Fin h)<⟨j-1,by omega⟩ from by
        change i-1 < j-1; omega)
      change (ballotDown S ⟨i-1,by omega⟩).val < (ballotDown S ⟨j-1,by omega⟩).val at k
      omega

lemma restored_cross (t : ℕ) (ht : t < h+1) : restoreU S (t+1) < restoreV S t := by
  rcases Nat.eq_zero_or_pos t with rfl|tp
  · simp
  rw [restoreU_other S (t+1) (by omega) (by omega),restoreV_other S t tp ht]
  have k := ballot_cross S ⟨t-1,by omega⟩
  have e : (⟨t+1-2,by omega⟩ : Fin h)=⟨t-1,by omega⟩ := Fin.ext (by change t+1-2=t-1; omega)
  rw [e]
  exact Nat.add_lt_add_left k 3

lemma restore_disjoint (i j : ℕ) (hi : i < h+2) (hj : j < h+2) :
    restoreU S i ≠ restoreV S j := by
  by_cases ilow : 2 ≤ i
  · rw [restoreU_other S i ilow hi]
    rcases Nat.eq_zero_or_pos j with rfl|jp
    · simp <;> omega
    by_cases jl : j = h+1
    · subst j
      rw [restoreV_last]
      have := (ballotUp S ⟨i-2,by omega⟩).isLt
      omega
    rw [restoreV_other S j jp (by omega)]
    intro he
    have E : ballotUp S ⟨i-2,by omega⟩ = ballotDown S ⟨j-1,by omega⟩ := Fin.ext (by omega)
    exact ballotDown_not_mem S _ (E ▸ ballotUp_mem S _)
  · rw [restoreU,dif_pos (show i < 2 by omega)]
    rcases Nat.eq_zero_or_pos j with rfl|jp
    · simp <;> omega
    by_cases jl : j = h+1
    · subst j; simp <;> omega
    rw [restoreV_other S j jp (by omega)]; omega

#print axioms restore_disjoint
end CoverCutoff
