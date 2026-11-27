import PetersenHalves

open scoped BigOperators
namespace PetersenStability

def mate (c : C) (v : V) : V :=
  ((List.finRange 15).find? fun a => full c a && (edge a v || edge v a)).getD 0

def sorted (a b : V) : V × V := if a.val < b.val then (a,b) else (b,a)
def firstEdge (c : C) (v : V) : V × V := sorted (mate c v) v
def secondEdge (c : C) (v : V) : V × V := (v, side c)
def active (c : C) : Finset (V × V) := E.filter (fun e => cover c e.1 e.2 = true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem active_eq : ∀ c : C,
    active c = (P c).image (firstEdge c) ∪ (P c).image (secondEdge c) := by decide

private theorem mate_full : ∀ c : C, ∀ v : V, v ∈ P c → full c (mate c v) = true := by decide

private theorem mate_image : ∀ c : C, (P c).image (mate c) = F c := by decide

private theorem mate_inj : ∀ c : C, ∀ a b : V, a ∈ P c → b ∈ P c →
    mate c a = mate c b → a = b := by decide

private theorem first_inj : ∀ c : C, ∀ a b : V, a ∈ P c → b ∈ P c →
    firstEdge c a = firstEdge c b → a = b := by decide

private theorem separate : ∀ c : C,
    Disjoint ((P c).image (firstEdge c)) ((P c).image (secondEdge c)) := by decide

noncomputable def cost (w : V → ℝ) (c : C) : ℝ :=
    ∑ e ∈ E, half w c e.1 * half w c e.2

theorem exact_cost (w : V → ℝ) (c : C) :
    cost w c = term (total w c) (w (anchor c)) (w (side c)) := by
  let f (e : V × V) := half w c e.1 * half w c e.2
  have hz : cost w c = ∑ e ∈ active c, f e := by
    unfold cost
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e he hn
    have hE : edge e.1 e.2 = true := (Finset.mem_filter.mp he).2
    have hC : cover c e.1 e.2 = false := by
      by_cases H : cover c e.1 e.2 = true
      · exact False.elim (hn (Finset.mem_filter.mpr ⟨he,H⟩))
      · simpa using H
    have ht := exactCover c e.1 e.2 hE
    rw [hC, Bool.and_eq_false_iff] at ht
    rcases ht with H | H
    · simp [f,half_zero _ _ _ H]
    · simp [f,half_zero _ _ _ H]
  have hP (v : V) (hv : v ∈ P c) : split c v = true := (Finset.mem_filter.mp hv).2
  have hh (v : V) (hv : v ∈ P c) :
      f (firstEdge c v) = w (mate c v) * (remainder w c / 3) := by
    dsimp [f, firstEdge, sorted]
    split <;> simp [half_full _ _ _ (mate_full c v hv), half_split _ _ _ (hP v hv), mul_comm]
  have hm : ∑ v ∈ P c, w (mate c v) = total w c := by
    unfold total
    rw [← mate_image c, Finset.sum_image]
    intro a ha b hb hab
    exact mate_inj c a b ha hb hab
  rw [hz, active_eq, Finset.sum_union (separate c)]
  rw [Finset.sum_image (fun a ha b hb hab => first_inj c a b ha hb hab)]
  rw [Finset.sum_image (fun a _ b _ hab => congrArg Prod.fst hab)]
  rw [Finset.sum_congr rfl hh, ← Finset.sum_mul, hm]
  have hh2 (v : V) (hv : v ∈ P c) :
      f (secondEdge c v) = remainder w c / 3 * (w (side c) / 4) := by
    simp [f,secondEdge,half_split _ _ _ (hP v hv),half_side]
  rw [Finset.sum_congr rfl hh2]
  simp [countP,term,remainder]
  ring

#print axioms exact_cost
end PetersenStability
