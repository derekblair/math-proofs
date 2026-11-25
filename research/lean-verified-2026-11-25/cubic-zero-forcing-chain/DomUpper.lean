import DomLower
namespace ZFChain
open Finset
set_option maxHeartbeats 1600000

def offsets (n : ℕ) := if (n+2)%3 = 2 then 2 else 1
def high {n} (i : Fin (n+2)) : Prop := i.val % 3 = offsets n
instance {n} (i : Fin (n+2)) : Decidable (high i) := by unfold high; infer_instance

theorem high_mid {n} {i : Fin (n+2)} (h : high i) : mid i = true := by
  unfold high offsets at h
  simp only [mid, decide_eq_true_eq]
  have := i.isLt
  split at h <;> omega

def domPick {n} (i : Fin (n+2)) : Finset (Fin 8) :=
  if high i then {2,6,7} else
  if mid i = true ∧ (i.val-1)%3 = offsets n then {1,4} else {0,3}

def chooseSet {n} (P : Fin (n+2) → Finset (Fin 8)) : Finset (V n) :=
  univ.filter (fun v => wire v ∈ P (blk v))
@[simp] theorem mem_chooseSet {n} (P : Fin (n+2) → Finset (Fin 8)) (v : V n) :
    v ∈ chooseSet P ↔ wire v ∈ P (blk v) := by simp [chooseSet]

theorem pull_chooseSet {n} (P : Fin (n+2) → Finset (Fin 8))
    (hP : ∀ i a, a ∈ P i → legal (mid i) a) (i : Fin (n+2)) :
    pull (chooseSet P) i = P i := by
  ext a
  constructor
  · intro ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    obtain ⟨hv,hi⟩ := mem_filter.mp hv
    simpa [hi] using (mem_chooseSet P v).mp hv
  · intro ha
    let v := lift i a (hP i a ha)
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨(mem_chooseSet P _).mpr ha,rfl⟩,rfl⟩

theorem card_chooseSet {n} (P : Fin (n+2) → Finset (Fin 8))
    (hP : ∀ i a, a ∈ P i → legal (mid i) a) :
    (chooseSet P).card = ∑ i : Fin (n+2), (P i).card := by
  simp_rw [← pull_chooseSet P hP,card_pull]
  rw [sum_card_fiberwise_eq_card_filter]
  simp

theorem domPick_legal {n} (i : Fin (n+2)) (a) (h : a ∈ domPick i) :
    legal (mid i) a := by
  by_cases hi : high i
  · exact Or.inl (high_mid hi)
  · unfold domPick at h
    simp only [hi, if_false] at h
    split at h
    · simp at h
      rcases h with rfl|rfl <;> exact Or.inr (by decide)
    · simp at h
      rcases h with rfl|rfl <;> exact Or.inr (by decide)

def good {n} (D : Finset (V n)) (x : V n) := x ∈ D ∨ ∃ y ∈ D, adj x y
theorem good_local {n} {D : Finset (V n)} (x : V n)
    (h : localDominates (mid (blk x)) (pull D (blk x)) (wire x)) : good D x := by
  rcases h with h|⟨a,ha⟩
  · exact Or.inl ((mem_pull D x).mp h)
  · obtain ⟨ha,haD⟩ := mem_inter.mp ha
    have he := (mem_filter.mp ha).2
    let y := lift (blk x) a (locEdge_legal _ _ _ he).2
    exact Or.inr ⟨y,(mem_pull D y).mp haD,(adj_same (x := x) (y := y) rfl).mpr he⟩

theorem dom_left_good {a : Fin 8} (ha : a ≠ 6) :
    localDominates true {1,4} a := by fin_cases a <;> revert ha <;> decide
theorem dom_right_good {a : Fin 8} (ha : a ≠ 7) :
    localDominates true {0,3} a := by fin_cases a <;> revert ha <;> decide
theorem dom_high_good (a : Fin 8) : localDominates true {2,6,7} a := by
  fin_cases a <;> decide
theorem dom_end_good {a : Fin 8} (ha : legal false a) :
    localDominates false {0,3} a := by fin_cases a <;> revert ha <;> decide

theorem high_count (n : ℕ) : (univ.filter (@high n)).card = (n+2)/3 := by
  have hor : offsets n = 1 ∨ offsets n = 2 := by unfold offsets; split <;> simp
  let f : Fin ((n+2)/3) ↪ Fin (n+2) :=
    ⟨fun j => ⟨3*j.val+offsets n, by have := j.isLt; omega⟩,
     fun a b h => Fin.ext (by
       have hh := congrArg Fin.val h
       change 3*a.val+offsets n = 3*b.val+offsets n at hh
       omega)⟩
  have hh : (univ : Finset (Fin ((n+2)/3))).map f = univ.filter (@high n) := by
    ext i
    simp only [mem_map, mem_univ, true_and, mem_filter,high]
    constructor
    · rintro ⟨j,rfl⟩
      change (3*j.val+offsets n)%3 = offsets n
      omega
    · intro hi
      have hh := i.isLt
      have hq : i.val/3 < (n+2)/3 := by
        unfold offsets at hi
        split at hi <;> omega
      exact ⟨⟨i.val/3,hq⟩,Fin.ext (by
        change 3*(i.val/3)+offsets n = i.val
        omega)⟩
  rw [← hh,card_map,card_univ,Fintype.card_fin]

theorem domPick_card {n} (i : Fin (n+2)) :
    (domPick i).card = 2+(if high i then 1 else 0) := by
  unfold domPick
  split
  · decide
  · split <;> decide

theorem domWitness (n : ℕ) : ∃ D : Finset (V n),
    Dominates D ∧ D.card = 2*(n+2)+(n+2)/3 := by
  let D := chooseSet (@domPick n)
  have hpull (i : Fin (n+2)) : pull D i = domPick i := pull_chooseSet _ domPick_legal i
  have hmem (y : V n) : y ∈ D ↔ wire y ∈ domPick (blk y) := mem_chooseSet _ _
  refine ⟨D,?_,?_⟩
  · intro x
    change good D x
    let i := blk x
    have fil (h : localDominates (mid i) (domPick i) (wire x)) : good D x := by
      apply good_local
      rw [hpull]
      exact h
    by_cases hh : high i
    · apply fil
      rw [high_mid hh]
      simpa [domPick,hh] using dom_high_good (wire x)
    by_cases hm : mid i = true
    · have hi : 0 < i.val ∧ i.val+1 < n+2 := by simpa [mid] using hm
      by_cases hl : (i.val-1)%3 = offsets n
      · by_cases hw : wire x = 6
        · let e : Fin (n+1) := ⟨i.val-1,by omega⟩
          have hx : x = right e := vertex_ext (Fin.ext (by change i.val = i.val-1+1; omega)) hw
          have hL : high e.castSucc := hl
          apply Or.inr
          refine ⟨left e, (hmem _).mpr ?_, Or.inr ?_⟩
          · simp [domPick,hL, out,high_mid hL]
          · exact ⟨e,Or.inr ⟨hx,rfl⟩⟩
        · apply fil
          simpa [domPick,hh,hm,hl] using dom_left_good hw
      · by_cases hw : wire x = 7
        · let e : Fin (n+1) := ⟨i.val,by omega⟩
          have hout : out e.castSucc = 7 := by
            have h : e.castSucc = i := Fin.ext rfl
            simp [out,h,hm]
          have hx : x = left e := vertex_ext (Fin.ext rfl) (by simpa [hout] using hw)
          have hR : high e.succ := by
            change (i.val+1)%3 = offsets n
            have h0 : i.val % 3 ≠ offsets n := hh
            unfold offsets at hl h0 ⊢
            split at hl <;> split at h0 <;> split <;> omega
          exact Or.inr ⟨right e,(hmem _).mpr (by simp [domPick,hR]),
             Or.inr ⟨e,Or.inl ⟨hx,rfl⟩⟩⟩
        · apply fil
          simpa [domPick,hh,hm,hl] using dom_right_good hw
    · have hm' : mid i = false := Bool.eq_false_iff.mpr hm
      have hp : legal (mid i) (wire x) := x.property
      rw [hm'] at hp
      apply fil
      simpa [domPick,hh,hm'] using dom_end_good hp
  · rw [card_chooseSet _ domPick_legal]
    simp_rw [domPick_card]
    rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin,sum_boole,high_count]
    change (n+2)*2 + (n+2)/3 = 2*(n+2)+(n+2)/3
    omega

end ZFChain
