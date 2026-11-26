import WeightedBits
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators

namespace QuorumMinimum

theorem projection_bad_card {A : Type} [Fintype A] [DecidableEq A] (r : Nat)
    (i : Fin (8*r) ↪ A) :
    (Finset.univ.filter (fun p : A → Bool => p ∘ i ∈ bad r)).card ≤
      2^(Fintype.card A-r) := by
  classical
  let q : A → Prop := fun a => a ∈ Set.range i
  let S := {a : A // ¬ q a}
  let e0 : Fin (8*r) ⊕ S ≃ A :=
    (Equiv.sumCongr (Equiv.ofInjective i i.injective) (Equiv.refl S)).trans (Equiv.sumCompl q)
  have eh (j : Fin (8*r)) : e0 (Sum.inl j) = i j := by
    rfl
  let e : (A → Bool) ≃ (Fin (8*r) → Bool) × (S → Bool) :=
    (Equiv.arrowCongr e0.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin (8*r)) S Bool)
  have ee (p : A → Bool) : (e p).1 = p ∘ i := by
    funext j
    change p (e0 (Sum.inl j))=p (i j)
    rw [eh]
  have hh : Fintype.card A = 8*r+Fintype.card S := by
    simpa using (Fintype.card_congr e0).symm
  calc
    _ = (bad r).card * 2^Fintype.card S := by
      simpa only [ee, Fintype.card_fun, Fintype.card_bool] using pullback_card e (bad r)
    _ ≤ 2^(7*r)*2^Fintype.card S := Nat.mul_le_mul_right _ (bad_card r)
    _ = 2^(Fintype.card A-r) := by rw [←pow_add,hh]; congr 1; omega

def flip {A : Type} : Equiv.Perm (A → Bool) where
  toFun p a := !p a
  invFun p a := !p a
  left_inv p := by funext a; simp
  right_inv p := by funext a; simp

theorem projection_flipped_bad_card {A : Type} [Fintype A] [DecidableEq A] (r : Nat)
    (i : Fin (8*r) ↪ A) :
    (Finset.univ.filter (fun p : A → Bool => (flip p) ∘ i ∈ bad r)).card ≤
      2^(Fintype.card A-r) := by
  classical
  let T : Finset (A → Bool) := Finset.univ.filter (fun p => p ∘ i ∈ bad r)
  have hh : Finset.univ.filter (fun p : A → Bool => (flip p) ∘ i ∈ bad r) =
      T.map (flip.symm.toEmbedding) := by
    ext w
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hw
      exact ⟨flip w, hw, flip.symm_apply_apply w⟩
    · rintro ⟨p,hp,h⟩
      simpa [←h] using hp
  rw [hh,Finset.card_map]
  exact projection_bad_card r i

/-- Simultaneous tail avoidance for both signs of every local projection. -/
theorem exists_balanced {A I : Type} [Fintype A] [Fintype I] (r L : Nat)
    (e : I → Fin (8*r) ↪ A) (small : Fintype.card I ≤ 2^L)
    (gap : L+1<r) :
    ∃ p : A → Bool, ∀ s, p ∘ e s ∉ bad r ∧ (flip p) ∘ e s ∉ bad r := by
  classical
  by_cases empty : IsEmpty I
  · exact ⟨fun _ => false, fun s => (empty.false s).elim⟩
  have pick : Nonempty I := not_isEmpty_iff.mp empty
  obtain ⟨s₀⟩ := pick
  have size : 8*r ≤ Fintype.card A := by
    simpa using Fintype.card_le_of_injective (e s₀) (e s₀).injective
  let badCase : Bool × I → Finset (A → Bool) := fun (b,s) =>
    Finset.univ.filter (fun p => (if b then flip p else p) ∘ e s ∈ bad r)
  have cap : ∀ i, (badCase i).card ≤ 2^(Fintype.card A-r) := by
    rintro ⟨b,s⟩
    cases b
    · exact projection_bad_card _ _
    · exact projection_flipped_bad_card _ _
  have strict : Fintype.card (Bool × I)*2^(Fintype.card A-r)<Fintype.card (A → Bool) := by
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool]
    calc
      2*Fintype.card I*2^(Fintype.card A-r)
          ≤ 2*2^L*2^(Fintype.card A-r) := by gcongr
      _ = 2^(L+1+(Fintype.card A-r)) := by rw [pow_add,pow_succ,Nat.mul_comm 2 (2^L)]
      _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨p,hp⟩ := exists_outside_family badCase _ cap strict
  refine ⟨p,fun s => ⟨?_,?_⟩⟩
  · simpa [badCase] using hp (false,s)
  · simpa [badCase] using hp (true,s)

#print axioms projection_bad_card
#print axioms exists_balanced

end QuorumMinimum
