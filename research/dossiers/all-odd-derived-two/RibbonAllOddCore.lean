import RibbonStationaryChart
import RibbonAllOddWordGraph
import RibbonAffineBase

namespace RibbonAllOddField
open RibbonAffine (Row Mono pl delta delta_zero eRow zeroRow march run_eval
  prodP prodP_sound poly_eq pl_mul subUV sub_sound avoid_neg rel_from_mul zpow_drop rel_drop
  parametric unit_pow_ok nf mulP mon)
variable {K G : Type*} [Field K] [Group G]

def symbol (k : Count) (i : Nat) : Row :=
  ((spec k).T.take i).foldl march zeroRow

theorem symbol_sound (μ : G →* Kˣ) (τ : G → K) (H : RibbonStationaryChart.Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (k : Count) (i : Nat) :
    let v := Ribbon5Bridge.pathAt x y (spec k).T.toArray i
    (v.1,μ v.2,τ v.2) = eRow (μ x) (μ y) (symbol k i) :=
  run_eval μ τ H.2 H.1 x y tx ty (Ribbon5Bridge.start G) zeroRow
    (by simp [eRow,pl,zeroRow,Ribbon5Bridge.start,H.1]) _

end RibbonAllOddField
