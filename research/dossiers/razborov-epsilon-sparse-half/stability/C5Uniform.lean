import StabilityTemplates
import StabilityDisturbed

open scoped BigOperators
namespace C5Stability

abbrev T := Fin 5
abbrev adj := PetersenStability.outer
abbrev E := SparseHalfStability.Edges adj

def nxt (i : T) : T := i+2
def partialV (i : T) : T := i+4

noncomputable def rem (w : T → ℝ) (i : T) := 1/2-w i-w (nxt i)
noncomputable def choice (w : T → ℝ) (i j : T) :=
  (if j=i then w j else 0) + (if j=nxt i then w j else 0) +
  (if j=partialV i then rem w i else 0)

def support (i j : T) := j=i ∨ j=nxt i ∨ j=partialV i
instance (i j : T) : Decidable (support i j) := inferInstanceAs (Decidable (_ ∨ _))

def sorted (a b : T) : T × T := if a < b then (a,b) else (b,a)
def port (i : T) := sorted i (partialV i)

private theorem neq : ∀ i : T, i ≠ nxt i ∧ i ≠ partialV i ∧ nxt i ≠ partialV i := by decide
private theorem exact : ∀ i : T,
    E.filter (fun e => support i e.1 ∧ support i e.2) = {port i} := by decide

private theorem cover : ∀ a b : T, a < b → adj a b = true → ∃ i, port i = (a,b) := by decide

private theorem part (w : T → ℝ) (i : T) : choice w i (partialV i) = rem w i := by
  simp [choice,(neq i).2.1.symm,(neq i).2.2.symm]
private theorem main (w : T → ℝ) (i : T) : choice w i i = w i := by
  simp [choice,(neq i).1,(neq i).2.1]

private theorem outside (w : T → ℝ) (i j : T) (h : ¬support i j) :
    choice w i j = 0 := by
  simp only [support, not_or] at h
  simp [choice,h.1,h.2.1,h.2.2]

structure Balanced (w : T → ℝ) : Prop where
  mass : ∑ i, w i = 1
  bounds : ∀ i, 9/50 ≤ w i ∧ w i ≤ 11/50

theorem mass (w : T → ℝ) (i : T) : ∑ j, choice w i j = 1/2 := by
  simp [choice, Finset.sum_add_distrib,rem]

theorem admissible (w : T → ℝ) (h : Balanced w) (i j : T) :
    0 ≤ choice w i j ∧ choice w i j ≤ w j := by
  have A := h.bounds i
  have B := h.bounds (nxt i)
  have C := h.bounds j
  by_cases H1 : j=i
  · subst j
    rw [main]
    constructor <;> linarith
  by_cases H2 : j=nxt i
  · subst j
    simp [choice, (neq i).1.symm, (neq i).2.2]
    linarith [B.1]
  by_cases H3 : j=partialV i
  · subst j
    rw [part]
    unfold rem
    constructor <;> linarith [(h.bounds (partialV i)).1]
  · simp [choice,H1,H2,H3]
    linarith

private theorem port_value (w : T → ℝ) (i : T) :
    choice w i (port i).1 * choice w i (port i).2 = w i * rem w i := by
  unfold port sorted
  split <;> simp [main,part,mul_comm]

noncomputable def cost (w : T → ℝ) (i : T) :=
  ∑ e ∈ E, choice w i e.1 * choice w i e.2

theorem exact_cost (w : T → ℝ) (i : T) : cost w i = w i * rem w i := by
  have hs : cost w i = ∑ e ∈ E.filter (fun e => support i e.1 ∧ support i e.2),
      choice w i e.1 * choice w i e.2 := by
    unfold cost
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hn
    have H : ¬(support i e.1 ∧ support i e.2) := fun H =>
      hn (Finset.mem_filter.mpr ⟨he,H⟩)
    by_cases a : support i e.1
    · have b : ¬ support i e.2 := fun b => H ⟨a,b⟩
      simp [outside w i e.2 b]
    · simp [outside w i e.1 a]
  rw [hs,exact]
  simpa using port_value w i

theorem uniform (w : T → ℝ) (h : Balanced w) (a b : T) (he : (a,b) ∈ E) :
    w a*w b/30 ≤ (∑ i, choice w i a * choice w i b)/5 := by
  obtain ⟨ha,hb⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨i,hi⟩ := cover a b ha hb
  have hh := port_value w i
  rw [hi] at hh
  have hsum := Finset.single_le_sum (f := fun j => choice w j a * choice w j b)
    (fun j _ => mul_nonneg (admissible w h j a).1 (admissible w h j b).1)
    (Finset.mem_univ i)
  rw [hh] at hsum
  have hfac : rem w i ≥ 3/50 := by unfold rem; linarith [(h.bounds i).2,(h.bounds (nxt i)).2]
  have hmass : w a*w b = w i*w (partialV i) := by
    unfold port sorted at hi
    split at hi
    · have h1 : i = a := congrArg Prod.fst hi
      have h2 : partialV i = b := congrArg Prod.snd hi
      rw [← h1,← h2]
    · have h1 : partialV i = a := congrArg Prod.fst hi
      have h2 : i = b := congrArg Prod.snd hi
      rw [← h1,← h2,mul_comm]
  rw [hmass]
  have hR : w (partialV i)/6 ≤ rem w i := by linarith [(h.bounds (partialV i)).2]
  have b := mul_le_mul_of_nonneg_left hR (by linarith [(h.bounds i).1] : 0 ≤ w i)
  nlinarith only [b,hsum]

theorem sparse_average (w : T → ℝ) (h : Balanced w) :
    (∑ i, cost w i)/5 ≤ 1/50 := by
  have hsum := h.mass
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at hsum
  simp only [exact_cost,rem,Fin.sum_univ_succ,Fin.sum_univ_zero]
  have hs := congrArg (·^2) hsum
  have p0 := sq_nonneg (w 0+w 2-2/5)
  have p1 := sq_nonneg (w 1+w 3-2/5)
  have p2 := sq_nonneg (w 2+w 4-2/5)
  have p3 := sq_nonneg (w 3+w 0-2/5)
  have p4 := sq_nonneg (w 4+w 1-2/5)
  change (w 0 * (1/2-w 0-w 2) + (w 1 * (1/2-w 1-w 3) +
    (w 2 * (1/2-w 2-w 4) + (w 3 * (1/2-w 3-w 0) +
    (w 4 * (1/2-w 4-w 1) + 0)))))/5 ≤ 1/50
  change w 0+(w 1+(w 2+(w 3+(w 4+0)))) = 1 at hsum
  nlinarith only [p0,p1,p2,p3,p4,hsum]

#print axioms sparse_average
#print axioms uniform
end C5Stability
