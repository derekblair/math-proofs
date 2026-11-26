import RibbonD3MateUse

namespace RibbonD3MateUse
open RibbonD3MateData RibbonD3SignedEval RibbonD3Grid RibbonD3PortEval RibbonDerived3
variable {G : Type*} [Group G]

def letters (C : Chart) (n : Nat) := erasePorts C.startSide (C.ports.toList.take n)
def ratio (C : Chart) (a b : Nat) := letters C b ++ inverse (letters C a)
def conjugator (r : RRow) := repeatPower 1 r.u ++ repeatPower 2 r.v
def reference (C : Chart) (r : RRow) :=
  conjugator r ++ (if r.sign == 1 then letters C 32 else inverse (letters C 32)) ++
    inverse (conjugator r)

def bounds (C : Chart) (r : RRow) : Bool :=
  r.leftWord < C.words.size && r.rightWord < C.words.size

private theorem boundsAll : (charts.all fun c => c.rows.all (bounds c)) = true := by decide +kernel

private theorem bounds_row (i : Fin charts.size) (j : Fin (charts[i]).rows.size) :
    bounds charts[i] (charts[i]).rows[j] = true := by
  have h := Array.all_eq_true.mp boundsAll i.val i.isLt
  exact Array.all_eq_true.mp h j.val j.isLt

theorem transcripts (i : Fin charts.size) (j : Fin (charts[i]).rows.size) :
    let C := charts[i]
    let r := C.rows[j]
    schreier C.keys (ratio C r.i r.j) = some C.words[r.leftWord]!.toList ∧
    schreier C.keys (reference C r) = some C.words[r.rightWord]!.toList ∧
    (r.sign = 1 ∨ r.sign = -1) := by
  dsimp
  have b := bounds_row i j
  simp only [bounds,Bool.and_eq_true_iff,decide_eq_true_eq] at b
  have c := checkR_true i j
  change (((charts[i]).rows[j].sign == 1 || (charts[i]).rows[j].sign == -1) &&
    schreier (charts[i]).keys (ratio charts[i] (charts[i]).rows[j].i (charts[i]).rows[j].j) ==
      ((charts[i]).words[(charts[i]).rows[j].leftWord]?).map Array.toList &&
    schreier (charts[i]).keys (reference charts[i] (charts[i]).rows[j]) ==
      ((charts[i]).words[(charts[i]).rows[j].rightWord]?).map Array.toList) = true at c
  simp only [Array.getElem?_eq_some_getElem! _ _ b.1,Array.getElem?_eq_some_getElem! _ _ b.2,
    Option.map_some,Bool.and_eq_true_iff,Bool.or_eq_true_iff,beq_iff_eq] at c
  exact ⟨c.1.2,c.2,c.1.1⟩

theorem legal_ratio (C : Chart) (i j : Nat) :
    ∀ z ∈ ratio C i j, legal z := by
  intro z h
  rcases List.mem_append.mp h with h|h
  · exact legal_erase _ _ z h
  · exact legal_inverse _ (legal_erase _ _) z h

theorem legal_conj (r : RRow) : ∀ z ∈ conjugator r, legal z := by
  intro z h
  rcases List.mem_append.mp h with h|h
  · exact legal_power (by unfold legal; decide) _ z h
  · exact legal_power (by unfold legal; decide) _ z h

theorem legal_reference (C : Chart) (r : RRow) :
    ∀ z ∈ reference C r, legal z := by
  intro z h
  rcases List.mem_append.mp h with h|h
  · rcases List.mem_append.mp h with h|h
    · exact legal_conj _ z h
    · by_cases e : r.sign == 1
      · exact legal_erase _ _ z (by simpa [e,letters] using h)
      · exact legal_inverse _ (legal_erase _ _) z (by simpa [e,letters] using h)
  · exact legal_inverse _ (legal_conj _) z h

/-- The actual x/y-word ratio and its conjugate reference agree modulo γ₃(D). -/
theorem mateR_mod (x y : G) (i : Fin charts.size) (j : Fin (charts[i]).rows.size) :
    let C := charts[i]
    let r := C.rows[j]
    eval (letter x y) (ratio C r.i r.j) *
      (eval (letter x y) (reference C r))⁻¹ ∈ DLS G 2 := by
  change eval (letter x y) (ratio charts[i] (charts[i]).rows[j].i (charts[i]).rows[j].j) *
      (eval (letter x y) (reference charts[i] (charts[i]).rows[j]))⁻¹ ∈ DLS G 2
  obtain ⟨L,R,_⟩ := transcripts i j
  rw [schreier_sound x y _ _ _ (legal_ratio _ _ _) L,
    schreier_sound x y _ _ _ (legal_reference _ _) R]
  exact dictionary_diff x y _ (Array.getElem_mem i.isLt) _ (Array.getElem_mem j.isLt)

#print axioms mateR_mod
end RibbonD3MateUse
