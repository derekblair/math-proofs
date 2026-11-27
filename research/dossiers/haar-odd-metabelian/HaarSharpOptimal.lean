import HaarSharpGeometry
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace HaarSharpLamp

def coordinates : G ≃ L × S where
  toFun g := ⟨g.left,g.right⟩
  invFun p := ⟨p.1,p.2⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro p; cases p; rfl

instance : Finite G := Finite.of_equiv _ coordinates.symm

theorem cardinality : Nat.card G = 7 * 3^14 := by
  rw [Nat.card_congr coordinates, Nat.card_prod]
  have h : Nat.card L = 3^14 := by
    simp [ZMod.card]
  rw [h]
  simp [ZMod.card]

theorem odd : Odd (Nat.card G) := by rw [cardinality]; decide

def projection : G →* Multiplicative S where
  toFun g := Multiplicative.ofAdd g.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem metabelian : ∀ a b : commutator G, a*b=b*a := by
  intro a b
  have ha := Abelianization.commutator_subset_ker projection a.property
  have hb := Abelianization.commutator_subset_ker projection b.property
  change a.val.right = 0 at ha
  change b.val.right = 0 at hb
  apply Subtype.ext
  apply G.ext'
  · intro t j
    change (mul a.val b.val).left t j = (mul b.val a.val).left t j
    simp [mul,ha,hb,add_comm]
  · change (mul a.val b.val).right = (mul b.val a.val).right
    simp [mul,ha,hb]

theorem x_nonid : x ≠ 1 := by
  intro e
  have h := congrArg G.right e
  change (1 : S) = 0 at h
  exact (by decide : (1:S) ≠ 0) h

theorem y_nonid : y ≠ 1 := by
  intro e
  have h := congrArg G.right e
  change (2 : S) = 0 at h
  exact (by decide : (2:S) ≠ 0) h

theorem xy_ne : x ≠ y := by
  intro e
  have h := congrArg G.right e
  change (1 : S) = 2 at h
  exact (by decide : (1:S) ≠ 2) h

/-- Explicit port word, written from the identity in the false part. -/
def witnessWord : Array (Fin 3) := #[1,0,1,0,1,0,1,0,1,0,1,2,0,1,0,1,0,1,0,1,0,2,1,2,1,0,1,2,1,0,2,0]

def step (a : Bool × G) (p : Fin 3) : Bool × G :=
  (!a.1, a.2 * oriented a.1 p)

theorem step_adj (a : Bool × G) (p : Fin 3) :
    HaarCycle.haarAdj x y a (step a p) := by
  obtain ⟨b,g⟩ := a
  cases b <;> fin_cases p <;> simp [HaarCycle.haarAdj,step,oriented,x,y,port0,mul_assoc]

def fromIdentity : Nat → Bool × G
  | 0 => (false,1)
  | k+1 => step (fromIdentity k) witnessWord[k]!

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem closing : fromIdentity 32 = fromIdentity 0 := by
  apply Prod.ext
  · decide +kernel
  · apply G.ext'
    · intro t j
      revert t j
      decide +kernel
    · decide +kernel

def vertex (i : Fin 32) : Bool × G := fromIdentity i.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem key_injective : Function.Injective
    (fun i : Fin 32 => ((vertex i).1,key (vertex i).2)) := by
  decide +kernel

theorem cycle32 : HaarAllNoncommuting.HasCycle x y 32 := by
  refine ⟨vertex,fun a b h => key_injective (congrArg (fun g : Bool × G => (g.1,key g.2)) h), ?_⟩
  intro i
  have e := step_adj (fromIdentity i.val) witnessWord[i.val]!
  change HaarCycle.haarAdj x y (fromIdentity i.val) (fromIdentity (i.val+1)) at e
  change HaarCycle.haarAdj x y (fromIdentity i.val) (fromIdentity ((i.val+1)%32))
  by_cases h : i.val+1 < 32
  · rw [Nat.mod_eq_of_lt h]; exact e
  · have h' : i.val+1 = 32 := by omega
    rw [h',Nat.mod_self,← closing]
    simpa only [h'] using e

theorem sharp : HaarAllNoncommuting.HasCycle x y 32 ∧
    ¬ HaarAllNoncommuting.HasCycle x y 4 ∧ ¬ HaarAllNoncommuting.HasCycle x y 8 ∧
    ¬ HaarAllNoncommuting.HasCycle x y 16 := ⟨cycle32, no_short_cycles⟩

#print axioms cardinality
#print axioms metabelian
#print axioms sharp
end HaarSharpLamp
