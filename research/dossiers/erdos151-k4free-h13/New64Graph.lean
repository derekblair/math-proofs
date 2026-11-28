import New64Mask
import Seed64Endpoint
import Mathlib.Data.Finset.Preimage

namespace Erdos151Ramsey.New64
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem graph_symm {a b : Fin 64} (h : graph a b) : graph b a := by
  have t : ∀ x y : Fin 64, graph x y → graph y x := by decide +kernel
  exact t _ _ h

theorem graph_irrefl : ∀ a : Fin 64, ¬ graph a a := by decide +kernel

private theorem triangle_check : ∀ a b : Fin 64,
    (adj a b = true) → (masks[a.val]! &&& masks[b.val]!) = 0 := by
  decide +kernel

theorem graph_triangle_free : TriangleFree graph := by
  intro a b c hab hbc hac
  have hz := congrArg (fun m : Nat => m.testBit c.val) (triangle_check a b hab)
  change masks[b.val]!.testBit c.val = true at hbc
  change masks[a.val]!.testBit c.val = true at hac
  simp [hbc, hac] at hz

def oldFun (x : Fin 63) : Fin 64 := ⟨(5*x.val)%63, by omega⟩

def oldInv (x : Fin 64) : Fin 63 := ⟨(38*x.val)%63, by omega⟩

theorem old_left : ∀ x : Fin 63, oldInv (oldFun x) = x := by decide +kernel

def old : Fin 63 ↪ Fin 64 where
  toFun := oldFun
  inj' := Function.LeftInverse.injective old_left

theorem old_right : ∀ x : Fin 64, x ≠ extra → old (oldInv x) = x := by decide +kernel

theorem old_edges : ∀ a b : Fin 63, Seed64.adj a b = true → graph (old a) (old b) := by
  decide +kernel

theorem old_bound (S : Finset (Fin 64)) (hex : extra ∉ S) (hind : Independent graph S) :
    S.card ≤ 13 := by
  let T : Finset (Fin 63) := S.preimage old old.injective.injOn
  have te : T.map old = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_preimage.mp ha
    · intro hx
      have xn : x ≠ extra := fun e=>hex (e ▸ hx)
      let a := oldInv x
      have e : old a = x := old_right x xn
      exact Finset.mem_map.mpr ⟨a, Finset.mem_preimage.mpr (e.symm ▸ hx),e⟩
  have ti : Independent Seed64.graph T := by
    intro a ha b hb hab
    exact hind (old a) (Finset.mem_preimage.mp ha) (old b) (Finset.mem_preimage.mp hb) (old_edges a b hab)
  have b := Seed64.alpha_le_thirteen T ti
  calc S.card = (T.map old).card := congrArg Finset.card te.symm
       _ = T.card := Finset.card_map old
       _ ≤ 13 := b

theorem alphaWitness_card : alphaWitness.card = 13 := by decide +kernel

theorem alphaWitness_ind : Independent graph alphaWitness := by
  change ∀ a ∈ alphaWitness, ∀ b ∈ alphaWitness, ¬ graph a b
  decide +kernel

end Erdos151Ramsey.New64
