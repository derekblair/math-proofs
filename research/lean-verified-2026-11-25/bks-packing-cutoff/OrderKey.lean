import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fin.Tuple.Basic

namespace CoverCutoff

open Finset

def keySet {n : ℕ} {α : Type} [LinearOrder α] (key : Fin n→α) : Finset α :=
  Finset.univ.image key

lemma keyCard {n : ℕ} {α : Type} [LinearOrder α] (key : Fin n→α)
    (hinj : Function.Injective key) : (keySet key).card=n := by
  unfold keySet
  rw [Finset.card_image_of_injective _ hinj]
  simp

noncomputable def keyToSet {n : ℕ} {α : Type} [LinearOrder α]
    (key : Fin n→α) (hinj : Function.Injective key) : Fin n ≃ keySet key :=
  Equiv.ofBijective (fun i => ⟨key i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact hinj (congrArg Subtype.val h)
    · rintro ⟨a,ha⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact ⟨i,rfl⟩)

/-- The unique ordinal ranks induced by injective comparison keys. -/
noncomputable def rankKey {n : ℕ} {α : Type} [LinearOrder α]
    (key : Fin n → α) (hinj : Function.Injective key) : Equiv.Perm (Fin n) :=
  (keyToSet key hinj).trans ((keySet key).orderIsoOfFin (keyCard key hinj)).symm.toEquiv

lemma rankKey_iff {n : ℕ} {α : Type} [LinearOrder α] (key : Fin n→α)
    (hinj : Function.Injective key) (a b : Fin n) :
    rankKey key hinj a < rankKey key hinj b ↔ key a < key b := by
  let e := ((keySet key).orderIsoOfFin (keyCard key hinj)).symm
  change e (keyToSet key hinj a) < e (keyToSet key hinj b) ↔ _
  rw [e.lt_iff_lt]
  rfl

lemma same_comparisons {n : ℕ} (p q : Equiv.Perm (Fin n))
    (h : ∀ i j, p i < p j ↔ q i < q j) : p=q := by
  let e : Fin n ≃o Fin n :=
    { toEquiv := p.symm.trans q
      map_rel_iff' := by
        intro a b
        have hh := h (p.symm b) (p.symm a)
        simp only [Equiv.apply_symm_apply] at hh
        simpa only [Equiv.trans_apply,not_lt] using not_congr hh.symm }
  ext i
  have H := Fin.coe_orderIso_apply e (p i)
  simpa [e] using H.symm

#print axioms rankKey_iff
#print axioms same_comparisons
end CoverCutoff
