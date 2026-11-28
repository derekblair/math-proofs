import N63TenTransport
import N63FiveRight

namespace Erdos151N63
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : V → V → Prop) [DecidableRel G]

theorem witnessFive_good (w : V) (R : Fin 4 ≃ {z : V // z≠w ∧ ¬G w z})
    (hD : fullDeg G w=5) (H : Array Nat)
    (rep : ∀ i j : Fin 4, adj H i.val j.val = decide (G (R i).val (R j).val))
    (sym : ∀ a b, G a b ↔ G b a) (irr : ∀ v, ¬G v v)
    (y : Fin 4) (hd : fullDeg G (R y).val≤5)
    (hg : rightGood5 H y.val (fullDeg G (R y).val)=true) :
    TenWitness G := by
  classical
  let t := fullDeg G (R y).val
  have mem (z : Fin 4) (hs : rightCandidate5 H y.val z.val=true) :
      z ∈ rightPool G (fun i => (R i).val) y := by
    unfold rightCandidate5 at hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hs
    have he := rep y z
    rw [hs.2] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨
      fun h => hs.1 (congrArg Fin.val h.symm),Finset.mem_univ _⟩,
      fun h => Bool.false_ne_true (he.trans (by simp [h]))⟩
  change rightGood5 H y.val t=true at hg
  unfold rightGood5 at hg
  by_cases h4 : 4≤t
  · rw [if_pos h4] at hg
    obtain ⟨z,hz,hzgood⟩ := List.any_eq_true.mp hg
    let Z : Fin 4 := ⟨z,List.mem_range.mp hz⟩
    have hP : priceOK 10 (fullDeg G w) t 1 := by
      rw [hD]
      have hcases : t=4 ∨ t=5 := by omega
      rcases hcases with h|h <;> rw [h] <;> exact minCenter_sound _ _ _ (by decide) (by decide) (by decide) (by decide)
    apply witness_right_pool G w R y {Z}
    · exact Finset.singleton_subset_iff.mpr (mem Z hzgood)
    · simpa [Erdos151Ramsey.Independent] using irr (R Z).val
    · simpa using hP
  · rw [if_neg h4] at hg
    by_cases ht : t=3
    · rw [if_pos ht] at hg
      obtain ⟨⟨a,b⟩,hp,hg⟩ := List.any_eq_true.mp hg
      obtain ⟨ha,hb,hab⟩ := (mem_pairs_iff 4 a b).mp hp
      let A : Fin 4 := ⟨a,ha⟩
      let B : Fin 4 := ⟨b,hb⟩
      have neq : A≠B := fun e => (Nat.ne_of_lt hab) (congrArg Fin.val e)
      simp only [Bool.and_eq_true,Bool.not_eq_true'] at hg
      have nAB : ¬G (R A).val (R B).val := by
        intro h
        have h' := rep A B
        rw [hg.2] at h'
        exact Bool.false_ne_true (h'.trans (by simp [h]))
      have hP : priceOK 10 (fullDeg G w) t 2 := by
        rw [hD,ht]
        exact minCenter_sound _ _ _ (by decide) (by decide) (by decide) (by decide)
      apply witness_right_pool G w R y {A,B}
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl|hz
        · exact mem A hg.1.1
        · have he := Finset.mem_singleton.mp hz
          subst z
          exact mem B hg.1.2
      · intro z hz v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz hv
        rcases hz with rfl|rfl <;> rcases hv with rfl|rfl
        · exact irr _
        · exact nAB
        · exact (sym _ _).not.mp nAB
        · exact irr _
      · simpa [Finset.card_insert_of_notMem,neq] using hP
    · simp [ht] at hg

#print axioms witnessFive_good
end Erdos151N63
