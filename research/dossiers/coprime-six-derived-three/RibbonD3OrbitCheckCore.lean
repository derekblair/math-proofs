import RibbonD3Orbit

namespace RibbonD3Finite

def PairOrbit (i : B) : Prop := ∀ j : B, i.val < j.val → PairResult i j
instance (i : B) : Decidable (PairOrbit i) := by unfold PairOrbit; infer_instance

def JetOrbit (i : B) : Prop := ∀ d : Direction i, JetResult i d
instance (i : B) : Decidable (JetOrbit i) := by unfold JetOrbit; infer_instance

def pairChunk (start : Nat) (i : Fin 8) : B := ⟨(start+i.val)%52,Nat.mod_lt _ (by decide)⟩

end RibbonD3Finite
