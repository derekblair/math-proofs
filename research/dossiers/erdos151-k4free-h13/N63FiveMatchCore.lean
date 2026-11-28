import N63FastCode
import N63TenPrice
namespace Erdos151N63
def matchRows (h : Nat) : List (Array Nat) :=
  let H := graphOfCode 4 h
  ((natTuples 16 (allowedMask 4 H) 5 0).filter (fun ts =>
    (rawDegreeOK 10 15 5 4 H ts) &&
    ((rawDegrees 5 4 H ts).drop 6).all (· == 3))).map (buildRaw 5 4 H)

theorem mem_matchRows (h : Nat) (f : Fin 5 → Fin 16)
    (hm : ∀ i j : Fin 5, i.val ≤ j.val → (f i).val ≤ (f j).val)
    (ha : ∀ i, allowed 4 (graphOfCode 4 h) (f i) = true)
    (hdeg : rawDegreeOK 10 15 5 4 (graphOfCode 4 h)
      ((List.finRange 5).map fun i => (f i).val) = true)
    (htail : ((rawDegrees 5 4 (graphOfCode 4 h)
      ((List.finRange 5).map fun i => (f i).val)).drop 6).all (· == 3) = true) :
    buildRows 5 4 (graphOfCode 4 h) f ∈ matchRows h := by
  unfold matchRows
  exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨
    mem_natTuples _ _ _ _ f hm (fun _ => Nat.zero_le _) ha, (by simp [hdeg,htail])⟩,rfl⟩

structure TenPivotEntry where
  rows : Array Nat
  x : Nat
  y : Nat
  center : List Nat
  deriving DecidableEq

def TenPivotEntry.cert (e : TenPivotEntry) : Prop :=
  pivotOK e.rows 10 e.x e.y e.center ∧
  priceOK 10 (deg e.rows 10 e.x) (deg e.rows 10 e.y) e.center.length

instance (e : TenPivotEntry) : Decidable e.cert := by
  unfold TenPivotEntry.cert
  infer_instance
end Erdos151N63
