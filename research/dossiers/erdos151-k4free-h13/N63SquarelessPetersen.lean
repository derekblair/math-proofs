import N63MooreDegree
import N63MooreModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum

namespace Erdos151N63
open H13PetersenComponents
set_option maxHeartbeats 0

private theorem match_two (T : Fin 2 → Fin 2 → Prop)
    (rows : ∀ i, (T i 0 ∧ ¬T i 1) ∨ (¬T i 0 ∧ T i 1))
    (cols : ∀ j, (T 0 j ∧ ¬T 1 j) ∨ (¬T 0 j ∧ T 1 j))
    (i j : Fin 2) :
    T i j ↔ (i=j ↔ T 0 0) := by
  have ra := rows 0
  have rb := rows 1
  have ca := cols 0
  have cb := cols 1
  fin_cases i <;> fin_cases j <;> norm_num <;> tauto

variable {V : Type*} [Fintype V] [DecidableEq V] (G : V → V → Prop) [DecidableRel G]

/-- The unique squareless cubic triangle-free graph on ten vertices
is Petersen, in the exact Kneser labels used by the coloring adapter. -/
theorem squareless_cubic_petersen (hn : Fintype.card V=10)
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (tf : ∀ v x y, G v x → G v y → ¬G x y)
    (sq : AtMostOneCommon G) (deg : ∀ v, fullDeg G v=3) :
    ∃ e : V ≃ Fin 10, ∀ x y, G x y ↔ PetersenAdj (e x) (e y) := by
  obtain ⟨w,L,M,bij,wL,mw,ml⟩ := moore_blocks G hn sym irr tf sq deg
  let a := decide (G (M 0 0) (M 1 0))
  let b := decide (G (M 0 0) (M 2 0))
  let c := decide (G (M 1 0) (M 2 0))
  have bit (i j : Fin 3) (h : i≠j) : matchFlag a b c i j = decide (G (M i 0) (M j 0)) := by
    fin_cases i <;> fin_cases j
    · exact (h rfl).elim
    · rfl
    · rfl
    · change decide (G (M 0 0) (M 1 0)) = decide (G (M 1 0) (M 0 0))
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using sym _ _
    · exact (h rfl).elim
    · rfl
    · change decide (G (M 0 0) (M 2 0)) = decide (G (M 2 0) (M 0 0))
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using sym _ _
    · change decide (G (M 1 0) (M 2 0)) = decide (G (M 2 0) (M 1 0))
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using sym _ _
    · exact (h rfl).elim
  have child (i j : Fin 3) (p q : Fin 2) :
      G (M i p) (M j q) ↔ i≠j ∧ ((p=q) ↔ matchFlag a b c i j=true) := by
    by_cases ne : i≠j
    · rw [bit i j ne]
      simp only [and_iff_right ne,decide_eq_true_eq]
      refine match_two (fun x y => G (M i x) (M j y)) ?_ ?_ p q
      · intro s
        exact moore_matching G w L M bij sym tf sq mw ml deg i j s ne
      · intro s
        have hm := moore_matching G w L M bij sym tf sq mw ml deg j i s ne.symm
        simpa only [sym (M j s) (M i 0),sym (M j s) (M i 1)] using hm
    · have e : i=j := not_ne_iff.mp ne
      subst j
      have hfalse := tf (L i) (M i p) (M i q) ((ml i i p).mpr rfl) ((ml i i q).mpr rfl)
      simp [hfalse]
  have rep (x y : MooreSlots) : modelAdj a b c x y ↔
      G (mooreVal w L M x) (mooreVal w L M y) := by
    rcases x with _|(i|⟨i,p⟩) <;> rcases y with _|(j|⟨j,q⟩) <;>
      simp only [modelAdj,mooreVal]
    · simp [irr]
    · simp [wL]
    · simp [mw]
    · simp [←sym w (L i),wL]
    · simp [tf w (L i) (L j) (wL i) (wL j)]
    · exact (ml i j q).symm
    · simp [←sym w (M i p),mw]
    · rw [eq_comm]; exact ((sym _ _).trans (ml j i p)).symm
    · exact (child i j p q).symm
  have mTF (v x y : MooreSlots) (ma : modelAdj a b c v x) (mb : modelAdj a b c v y) :
      ¬modelAdj a b c x y :=
    fun h => tf _ _ _ ((rep _ _).mp ma) ((rep _ _).mp mb) ((rep _ _).mp h)
  obtain ⟨bp,hp⟩ := model_checked a b c mTF
  let he : MooreSlots ≃ V := Equiv.ofBijective _ bij
  let pe : MooreSlots ≃ Fin 10 := Equiv.ofBijective _ bp
  refine ⟨he.symm.trans pe,?_⟩
  intro x y
  have hx : mooreVal w L M (he.symm x)=x := he.apply_symm_apply x
  have hy : mooreVal w L M (he.symm y)=y := he.apply_symm_apply y
  have r := (rep (he.symm x) (he.symm y)).symm.trans (hp _ _)
  change G x y ↔ PetersenAdj (modelPerm a b c (he.symm x)) (modelPerm a b c (he.symm y))
  simpa only [hx,hy] using r

#print axioms squareless_cubic_petersen
end Erdos151N63
