import N63BuildMasks
import Mathlib.Data.Fintype.EquivFin

namespace Erdos151N63
abbrev Slot (d q : Nat) := Option (Fin d ⊕ Fin q)

def indexVal {d q : Nat} : Slot d q → Nat
  | none => 0
  | some (Sum.inl i) => i.val+1
  | some (Sum.inr j) => d+1+j.val

def indexFin (d q : Nat) (n : Nat) (hn : d+q+1=n) (i : Slot d q) : Fin n :=
  ⟨indexVal i,by
    rcases i with _|(_|_) <;> simp [indexVal] <;> omega⟩

theorem indexFin_bij (d q n : Nat) (hn : d+q+1=n) : Function.Bijective (indexFin d q n hn) := by
  constructor
  · intro a b h
    have he := congrArg Fin.val h
    change indexVal a=indexVal b at he
    rcases a with _|(a|a) <;> rcases b with _|(b|b) <;>
      simp only [indexVal,Option.some.injEq,Sum.inl.injEq,Sum.inr.injEq, Fin.ext_iff] at he ⊢ <;>
      try omega
  · intro i
    by_cases hz : i.val=0
    · exact ⟨none,Fin.ext hz.symm⟩
    by_cases hd : i.val≤d
    · exact ⟨some (Sum.inl ⟨i.val-1,by omega⟩),Fin.ext (by
        change i.val-1+1=i.val
        omega)⟩
    · exact ⟨some (Sum.inr ⟨i.val-(d+1),by omega⟩),Fin.ext (by
        change d+1+(i.val-(d+1))=i.val
        omega)⟩

noncomputable def indexEquiv (d q n : Nat) (hn : d+q+1=n) : Slot d q ≃ Fin n :=
  Equiv.ofBijective (indexFin d q n hn) (indexFin_bij d q n hn)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop)
def slotVal (w : V) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z})
    (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z}) : Slot d q → V
  | none => w
  | some (Sum.inl i) => (L i).val
  | some (Sum.inr j) => (R j).val

theorem slotVal_bij (w : V) (irr : ¬G w w) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z})
    (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z}) : Function.Bijective (slotVal G w L R) := by
  classical
  constructor
  · intro a b h
    rcases a with _|(a|a) <;> rcases b with _|(b|b) <;> simp only [slotVal] at h
    · rfl
    · have hh := (L b).property
      rw [←h] at hh
      exact False.elim (irr hh)
    · exact False.elim ((R b).property.1 h.symm)
    · have hh := (L a).property
      rw [h] at hh
      exact False.elim (irr hh)
    · exact congrArg (fun x => some (Sum.inl x)) (L.injective (Subtype.ext h))
    · exact False.elim ((R b).property.2 (h ▸ (L a).property))
    · exact False.elim ((R a).property.1 h)
    · exact False.elim ((R a).property.2 (h.symm ▸ (L b).property))
    · exact congrArg (fun x => some (Sum.inr x)) (R.injective (Subtype.ext h))
  · intro z
    by_cases hz : z=w
    · exact ⟨none,hz.symm⟩
    by_cases hz' : G w z
    · obtain ⟨i,hi⟩ := L.surjective ⟨z,hz'⟩
      exact ⟨some (Sum.inl i),congrArg Subtype.val hi⟩
    · obtain ⟨j,hj⟩ := R.surjective ⟨z,hz,hz'⟩
      exact ⟨some (Sum.inr j),congrArg Subtype.val hj⟩

noncomputable def slotEquiv (w : V) (irr : ¬G w w) {d q : Nat}
    (L : Fin d ≃ {z : V // G w z})
    (R : Fin q ≃ {z : V // z≠w ∧ ¬G w z}) : Slot d q ≃ V :=
  Equiv.ofBijective _ (slotVal_bij G w irr L R)

#print axioms indexFin_bij
#print axioms slotVal_bij
end Erdos151N63
