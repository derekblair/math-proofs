import N63Moore
import PetersenComponents

namespace Erdos151N63
open H13PetersenComponents
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def matchFlag (a b c : Bool) (i j : Fin 3) : Bool :=
  if i=0 ∧ j=1 ∨ i=1 ∧ j=0 then a else
    if i=0 ∧ j=2 ∨ i=2 ∧ j=0 then b else c

def modelAdj (a b c : Bool) : MooreSlots → MooreSlots → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | some (Sum.inl i), some (Sum.inr (j,_)) => i=j
  | some (Sum.inr (i,_)), some (Sum.inl j) => i=j
  | some (Sum.inr (i,p)), some (Sum.inr (j,q)) => i≠j ∧ ((p=q) ↔ matchFlag a b c i j=true)
  | _,_ => False

instance (a b c : Bool) (x y : MooreSlots) : Decidable (modelAdj a b c x y) := by

  rcases x with _|(_|⟨_,_⟩) <;> rcases y with _|(_|⟨_,_⟩) <;>
    unfold modelAdj <;> infer_instance

def modelIndex : MooreSlots → Nat
  | none => 0
  | some (Sum.inl i) => i.val+1
  | some (Sum.inr (i,j)) => 4+2*i.val+j.val

def rawPerm (a b c : Bool) : Array Nat :=
  match a,b,c with
  | false,false,false => #[0,7,8,9,3,6,2,5,1,4]
  | false,true,true => #[0,7,8,9,3,6,2,5,4,1]
  | true,false,true => #[0,7,8,9,3,6,5,2,1,4]
  | true,true,false => #[0,7,8,9,3,6,5,2,4,1]
  | _,_,_ => #[]

def modelPerm (a b c : Bool) (x : MooreSlots) : Fin 10 :=
  ⟨(mask (rawPerm a b c) (modelIndex x)) % 10, Nat.mod_lt _ (by decide)⟩

instance (a b : Fin 10) : Decidable (PetersenAdj a b) := inferInstanceAs
  (Decidable (PetersenMask a &&& PetersenMask b=0))

private def PermCert (a b c : Bool) : Prop :=
  (∀ x y : MooreSlots, modelPerm a b c x = modelPerm a b c y → x=y) ∧
  (∀ j : Fin 10, ∃ x : MooreSlots, modelPerm a b c x=j) ∧
  ∀ x y : MooreSlots, modelAdj a b c x y ↔ PetersenAdj (modelPerm a b c x) (modelPerm a b c y)

instance (a b c : Bool) : Decidable (PermCert a b c) := by
  unfold PermCert
  infer_instance

def rightSlot (i : Fin 3) (j : Fin 2) : MooreSlots := some (Sum.inr (i,j))

theorem model_checked (a b c : Bool)
    (tf : ∀ v x y, modelAdj a b c v x → modelAdj a b c v y → ¬modelAdj a b c x y) :
    Function.Bijective (modelPerm a b c) ∧
      ∀ x y, modelAdj a b c x y ↔ PetersenAdj (modelPerm a b c x) (modelPerm a b c y) := by
  have finish (h : PermCert a b c) : Function.Bijective (modelPerm a b c) ∧
      ∀ x y, modelAdj a b c x y ↔ PetersenAdj (modelPerm a b c x) (modelPerm a b c y) := ⟨⟨fun _ _ e => h.1 _ _ e,h.2.1⟩, h.2.2⟩
  cases a <;> cases b <;> cases c
  · exact finish (by decide +kernel)
  · exact False.elim (tf (rightSlot 0 0) (rightSlot 1 1) (rightSlot 2 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · exact False.elim (tf (rightSlot 0 0) (rightSlot 1 1) (rightSlot 2 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · exact finish (by decide +kernel)
  · exact False.elim (tf (rightSlot 0 0) (rightSlot 1 0) (rightSlot 2 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · exact finish (by decide +kernel)
  · exact finish (by decide +kernel)
  · exact False.elim (tf (rightSlot 0 0) (rightSlot 1 0) (rightSlot 2 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

#print axioms model_checked
end Erdos151N63
