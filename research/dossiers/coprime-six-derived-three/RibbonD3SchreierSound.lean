import RibbonD3GridEval

namespace RibbonD3Grid
open RibbonD3MateData RibbonD3SignedEval
variable {G : Type*} [Group G]

theorem fold_telescope (x y : G) (keys : Array Coord) (w : List Int)
    (hw : ∀ a ∈ w, legal a) (q t : State)
    (H : w.foldlM (gstep keys) q = some t) :
    meaning x y keys t = meaning x y keys q * eval (letter x y) w := by
  induction w generalizing q with
  | nil =>
    simp at H
    subst t
    simp [eval]
  | cons a w ih =>
    rw [List.foldlM_cons] at H
    cases E : gstep keys q a with
    | none => simp [E] at H
    | some z =>
      have Hz : w.foldlM (gstep keys) z = some t := by simpa [E] using H
      rw [ih (fun d hd => hw d (List.mem_cons_of_mem _ hd)) z Hz]
      rw [step_sound x y keys (hw a (by simp)) E]
      simp [eval,mul_assoc]

private theorem redStep_legal (q : List Int) (a : Int)
    (hq : ∀ v ∈ q, legal v) (ha : legal a) :
    ∀ v ∈ redStep q a, legal v := by
  intro v hv
  cases q with
  | nil =>
    have E : v = a := by simpa [redStep] using hv
    rwa [E]
  | cons p q =>
    by_cases h : p = -a
    · simp [redStep,h] at hv
      exact hq v (List.mem_cons_of_mem _ hv)
    · simp [redStep,h] at hv
      rcases hv with hv|hv|hv
      · rwa [hv]
      · exact hq v (by simp [hv])
      · exact hq v (by simp [hv])

private theorem redFold_legal (w q : List Int)
    (hw : ∀ a ∈ w, legal a) (hq : ∀ a ∈ q, legal a) :
    ∀ a ∈ w.foldl redStep q, legal a := by
  induction w generalizing q with
  | nil => exact hq
  | cons b w ih =>
    exact ih (redStep q b) (fun v hv => hw v (List.mem_cons_of_mem _ hv))
      (redStep_legal q b hq (hw b (by simp)))

theorem freeReduce_legal (w : List Int) (hw : ∀ a ∈ w, legal a) :
    ∀ a ∈ freeReduce w, legal a := by
  intro a ha
  change a ∈ (w.foldl redStep []).reverse at ha
  exact redFold_legal w [] hw (by simp) a (by simpa using ha)

/-- If the certified Schreier computation succeeds, the corresponding
group word is exactly the evaluation of its grid-edge letter list. -/
theorem schreier_sound (x y : G) (keys : Array Coord) (w out : List Int)
    (hw : ∀ a ∈ w, legal a) (H : schreier keys w = some out) :
    eval (letter x y) w = eval (indexed x y keys) out := by
  let red := freeReduce w
  change ((red.foldlM (gstep keys) (0,0,[])).bind (fun (i,j,q) =>
      if i == 0 && j == 0 then some q.reverse else none)) = some out at H
  cases E : red.foldlM (gstep keys) (0,0,[]) with
  | none => simp [E] at H
  | some T =>
    obtain ⟨i,j,q⟩ := T
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl,rfl⟩ := h
      simp [E] at H
      subst out
      have G := fold_telescope x y keys red (freeReduce_legal w hw) (0,0,[]) (0,0,q) E
      simpa [meaning,trans,eval,red,freeReduce_sound _ (neg_letter x y)] using G.symm
    · simp [E,h] at H

#print axioms schreier_sound
end RibbonD3Grid
