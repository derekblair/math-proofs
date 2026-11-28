import CoreExtract

namespace Erdos151H13.Kneser
set_option maxRecDepth 8000
set_option maxHeartbeats 0

def subsets : Array Nat := #[3, 5, 9, 17, 33, 65, 6, 10, 18, 34, 66, 12, 20, 36, 68, 24, 40, 72, 48, 80, 96]
def colorRows : Array Nat := #[1835008, 1835008, 1074688, 76480, 39360, 39360, 1835064, 1835064, 1245232, 688140, 360452, 1835064, 1245232, 688140, 360452, 1074736, 546056, 275200, 150723, 76483, 39367]

def Adj (i j : Fin 21) : Prop := (subsets[i.val]! &&& subsets[j.val]!) = 0
instance : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable (_ = _))
def color (i j : Fin 21) : Bool := colorRows[i.val]!.testBit j.val

theorem colorSymm : ∀ i j, color i j = color j i := by
  decide +kernel

theorem colorSafe : BikovLocal.Safe Adj color := by
  unfold BikovLocal.Safe
  decide +kernel

theorem pullback_color {V : Type*} (G : V → V → Prop) (f : V → Fin 21)
    (pres : ∀ {a b}, G a b → Adj (f a) (f b)) : ¬ BikovLocal.Ramsey G := by
  intro h
  exact h (fun a b => color (f a) (f b)) (fun a b => colorSymm (f a) (f b))
    (fun a b c ha hb hc => colorSafe _ _ _ (pres ha) (pres hb) (pres hc))

#print axioms colorSafe
#print axioms pullback_color
end Erdos151H13.Kneser
