import RibbonD3FieldPoint

namespace RibbonD3FieldPoint
open RibbonD3WordSelection RibbonD3VertexMates RibbonDerived3
variable {G K : Type*} [Group G] [Field K]

theorem from_affine (d3 : DLS G 3 = ⊥) (x y : G) (k : Count) (μ : G →* Kˣ) (τ : G → K)
    (co : RibbonStationaryChart.Aff μ τ) (tx : τ x = 0) (ty : τ y = 1)
    (sep : RibbonD3Field.Separates (RibbonD3Field.chart k) (μ x) (μ y)) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 ∨ Ribbon.Cycle x y 128 :=
  RibbonD3ChartCycles.from_chart d3 x y k
    (fun a b h => sep a b (affine_collision μ τ co x y tx ty k a.val b.val h))

#print axioms from_affine
end RibbonD3FieldPoint
