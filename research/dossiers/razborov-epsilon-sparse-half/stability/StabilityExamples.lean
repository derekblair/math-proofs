import StabilityLocal
open scoped BigOperators
namespace SparseHalfStability

def pEmbed (i : Fin 10) : Fin 15 := ⟨i.val,by omega⟩

private theorem pSym (a b : Fin 15) :
    PetersenStability.adj a b = PetersenStability.adj b a := Bool.or_comm _ _

private theorem pEdges :
    Edges PetersenStability.adj = PetersenStability.E := by decide

private theorem pPattern (s : Finset (Fin 10))
    (hs : ∀ i ∈ s, ∀ j ∈ s, PetersenStability.adj (pEmbed i) (pEmbed j) = false) :
    ∃ a, ∀ i ∈ s, PetersenStability.adj a (pEmbed i) = true := by
  have hm : s.image pEmbed ⊆ PetersenStability.base := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩
  have hInd : PetersenStability.independent (s.image pEmbed) := by
    intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    exact hs i hi j hj
  obtain ⟨a,ha⟩ := PetersenStability.petersen_pattern _ hm hInd
  exact ⟨a,fun i hi => (pSym _ _).trans (ha _ (Finset.mem_image_of_mem _ hi))⟩

private theorem pCodeg (a b : Fin 15) (h : PetersenStability.adj a b = false) :
    ∃ i, PetersenStability.adj a (pEmbed i) = true ∧
      PetersenStability.adj b (pEmbed i) = true := by
  obtain ⟨j,hj,h1,h2⟩ := PetersenStability.petersen_common a b h
  exact ⟨⟨j.val,hj⟩,h1,h2⟩

private theorem pAdj_order : ∀ a b : Fin 15, a < b →
    (PetersenStability.adj a b = true → PetersenStability.edge a b = true) := by decide

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Finite edit stability of the Petersen blowup, with conservative explicit
constants. The discrepancy counts directed pairs, twice the unordered edit count. -/
theorem petersen_edit_stability (G : V → V → Bool) (p : V → Fin 10)
    (sym : ∀ u v, G u v = G v u)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (hn : 0 < Fintype.card V)
    (edits : ((directedErrors G (fun i j => PetersenStability.adj (pEmbed i) (pEmbed j)) p).card : ℝ)
      ≤ ((Fintype.card V : ℝ)/10000000)^2)
    (balance : ∀ i, (99/1000 : ℝ)*(Fintype.card V : ℝ) ≤ (fiber p i).card) :
    HasSparseFractional G := by
  let n : ℝ := Fintype.card V
  have np : 0 < n := by dsimp [n]; exact_mod_cast hn
  refine local_of_chart (J := Fin 20) PetersenStability.adj G p pEmbed sym pSym
    PetersenStability.petersen_loopless tf pPattern pCodeg
    (1/80) (1/100000) (n/10000000) (49/500)
    (by norm_num) (by norm_num) (by norm_num) (div_pos np (by norm_num)) ?_ hn edits ?_ ?_ (by infer_instance) ?_
  · norm_num [Fintype.card_fin]
    change _ ≤ 1/100000*n
    linarith [np.le]
  · intro i
    linarith [balance i]
  · intro i
    change 49/500*n+n/10000000 ≤ _
    linarith [balance i]
  · intro w nonneg mass low
    have lo : ∀ t : Fin 15, t.val < 10 → (49/500 : ℝ) ≤ w t :=
      fun t ht => low ⟨t.val,ht⟩
    have hb : PetersenStability.Balanced w := ⟨nonneg,mass,lo⟩
    refine ⟨PetersenStability.half w,
      PetersenStability.admissible w hb,PetersenStability.mass w,?_,?_⟩
    · intro a b h
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · have H := PetersenStability.uniform w hb a b (pAdj_order a b hlt h)
        norm_num
        nlinarith only [H]
      · simp [PetersenStability.petersen_loopless] at h
      · have H := PetersenStability.uniform w hb b a (pAdj_order b a hgt ((pSym b a).trans h))
        simp_rw [mul_comm (PetersenStability.half w _ b)] at H
        rw [mul_comm (w b)] at H
        norm_num
        nlinarith only [H]
    · have H := PetersenStability.sparse_average w hb
      unfold edgeCost
      rw [pEdges]
      change (∑ i, PetersenStability.cost w i) ≤ _
      norm_num
      linarith

private theorem c5Sym : ∀ a b : Fin 5, C5Stability.adj a b = C5Stability.adj b a := by decide
private theorem c5Loop : ∀ a : Fin 5, C5Stability.adj a a = false := by decide

private theorem c5Pattern (s : Finset (Fin 5))
    (hs : ∀ i ∈ s, ∀ j ∈ s, C5Stability.adj i j = false) :
    ∃ a, ∀ i ∈ s, C5Stability.adj a i = true := by
  obtain ⟨a,h⟩ := PetersenStability.c5_pattern s hs
  exact ⟨a,fun i hi => (c5Sym a i).trans (h i hi)⟩

private theorem c5_bal (w : Fin 5 → ℝ) (mass : ∑ i,w i = 1)
    (h : ∀ i, (39/200 : ℝ) ≤ w i) : C5Stability.Balanced w := by
  refine ⟨mass, ?_⟩
  intro i
  refine ⟨by linarith [h i],?_⟩
  have hs := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ i)
  rw [mass] at hs
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)).erase i) (fun j _ => h j)
  simp [Finset.card_erase_of_mem (Finset.mem_univ i)] at hh
  linarith

theorem c5_edit_stability (G : V → V → Bool) (p : V → Fin 5)
    (sym : ∀ u v, G u v = G v u)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (hn : 0 < Fintype.card V)
    (edits : ((directedErrors G C5Stability.adj p).card : ℝ) ≤ ((Fintype.card V : ℝ)/10000000)^2)
    (balance : ∀ i, (199/1000 : ℝ)*(Fintype.card V : ℝ) ≤ (fiber p i).card) :
    HasSparseFractional G := by
  let n : ℝ := Fintype.card V
  have np : 0 < n := by dsimp [n]; exact_mod_cast hn
  refine local_of_chart (J := Fin 5) C5Stability.adj G p id sym c5Sym c5Loop tf
    c5Pattern PetersenStability.c5_common (1/30) (1/100000) (n/10000000) (39/200)
    (by norm_num) (by norm_num) (by norm_num) (div_pos np (by norm_num)) ?_ hn edits ?_ ?_ (by infer_instance) ?_
  · norm_num [Fintype.card_fin]
    change _ ≤ 1/100000*n
    linarith [np.le]
  · intro i
    linarith [balance i]
  · intro i
    change 39/200*n+n/10000000 ≤ _
    linarith [balance i]
  · intro w _ mass low
    have hb := c5_bal w mass low
    refine ⟨C5Stability.choice w, C5Stability.admissible w hb,C5Stability.mass w,?_,?_⟩
    · intro a b h
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · have H := C5Stability.uniform w hb a b
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt,h⟩)
        norm_num
        nlinarith only [H]
      · simp [c5Loop] at h
      · have H := C5Stability.uniform w hb b a
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgt,(c5Sym b a).trans h⟩)
        simp_rw [mul_comm (C5Stability.choice w _ b)] at H
        rw [mul_comm (w b)] at H
        norm_num
        nlinarith only [H]
    · have H := C5Stability.sparse_average w hb
      change (∑ i, C5Stability.cost w i) ≤ _
      norm_num
      linarith

#print axioms petersen_edit_stability
#print axioms c5_edit_stability
end SparseHalfStability
