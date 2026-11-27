import StabilityDisturbed

open scoped BigOperators
namespace SparseHalfStability

variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]

def fiber (p : V → T) (i : T) : Finset V :=
  Finset.univ.filter fun x => p x = i

def near (G : V → V → Bool) (p : V → T) (v : V) (i : T) : Finset V :=
  (fiber p i).filter (fun x => G v x = true)

def err (G : V → V → Bool) (H : T → T → Bool) (p : V → T) (v : V) : Finset V :=
  Finset.univ.filter (fun x => G v x ≠ H (p v) (p x))

noncomputable def heavy (G : V → V → Bool) (p : V → T) (τ : ℝ) (v : V) : Finset T := by
  classical
  exact Finset.univ.filter (fun i => τ < ((near G p v i).card : ℝ))

def directedErrors (G : V → V → Bool) (H : T → T → Bool) (p : V → T) :
    Finset (V × V) :=
  Finset.univ.filter (fun e => G e.1 e.2 ≠ H (p e.1) (p e.2))

theorem heavy_independent (G : V → V → Bool) (H : T → T → Bool) (p : V → T)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (τ : ℝ) (hn : 0 ≤ τ) (hb : ((directedErrors G H p).card : ℝ) ≤ τ^2)
    (v : V) (i j : T) (hi : i ∈ heavy G p τ v) (hj : j ∈ heavy G p τ v) :
    H i j = false := by
  classical
  have hi' : τ < ((near G p v i).card : ℝ) := (Finset.mem_filter.mp hi).2
  have hj' : τ < ((near G p v j).card : ℝ) := (Finset.mem_filter.mp hj).2
  by_contra h
  have hh : H i j = true := by simpa using h
  have hsub : (near G p v i).product (near G p v j) ⊆ directedErrors G H p := by
    intro e he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp he
    obtain ⟨ha,ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hb'⟩ := Finset.mem_filter.mp hb
    have hp := (Finset.mem_filter.mp ha).2
    have hq := (Finset.mem_filter.mp hb).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [tf v e.1 e.2 ha' hb', hp,hq,hh]
    decide
  have hs := Finset.card_le_card hsub
  have hcard := Finset.card_product (s := near G p v i) (t := near G p v j)
  change ((near G p v i).product (near G p v j)).card = _ at hcard
  rw [hcard] at hs
  have hs' : ((near G p v i).card : ℝ)*(near G p v j).card ≤
      (directedErrors G H p).card := by exact_mod_cast hs
  have hp := mul_lt_mul_of_pos_right hi' (hn.trans_lt hj')
  have hp2 := mul_le_mul_of_nonneg_left hj'.le hn
  nlinarith

/-- If two original labels are nonadjacent and both endpoints have few
incident errors, their large shared template cell rules out an added edge. -/
theorem good_pair (G : V → V → Bool) (H : T → T → Bool) (p : V → T)
    (tf : ∀ u v w, G u v = true → G u w = true → G v w = false)
    (τ : ℝ) (u v : V) (i : T) (hi : H (p u) i = true) (hj : H (p v) i = true)
    (hu : ((err G H p u).card : ℝ) ≤ τ) (hv : ((err G H p v).card : ℝ) ≤ τ)
    (cell : 2*τ < ((fiber p i).card : ℝ)) :
    G u v = false := by
  by_contra h
  have hg : G u v = true := by simpa using h
  have cover : fiber p i ⊆ err G H p u ∪ err G H p v := by
    intro z hz
    have hp' := (Finset.mem_filter.mp hz).2
    by_cases A : G u z = true
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [tf u v z hg A,hp',hj]; decide⟩
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hp',hi] using A⟩
  have hle := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have hle' : ((fiber p i).card : ℝ) ≤ (err G H p u).card + (err G H p v).card := by
    exact_mod_cast hle
  linarith

#print axioms heavy_independent
#print axioms good_pair
end SparseHalfStability
