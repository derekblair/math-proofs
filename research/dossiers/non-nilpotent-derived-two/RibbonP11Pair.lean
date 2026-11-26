import RibbonP11Charts

namespace RibbonP11Pair
open RibbonStationaryWord RibbonP11Charts
abbrev F := ZMod 11
abbrev Parameter := F × F
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def bad : Fin 16 → Parameter :=
  ![(1,3),(1,4),(1,5),(1,9),(3,1),(3,3),(3,4),(4,1),(4,3),(4,4),
    (5,1),(5,5),(5,9),(9,1),(9,5),(9,9)]

def point (z : Parameter) (k : Count) (i : Fin 64) : Flat F :=
  flatPosition z.1 (z.1^9) z.2 (z.2^9) (if z.1=1 then 1 else 0)
    (if z.1=1 then 0 else 1) (spec k) i.val

def property (k : Count) (p q : Parameter) : Prop :=
  ∀ i j : Fin 64, i.val<j.val → point p k i=point p k j → point q k i=point q k j →
    IsMate (spec k) i.val j.val
instance (k : Count) (p q : Parameter) : Decidable (property k p q) := by unfold property; infer_instance

end RibbonP11Pair
