import RibbonD3ChartCycles

namespace RibbonD3FieldPoint
open RibbonD3MateData RibbonD3PortEval RibbonD3WordSelection RibbonD3VertexMates Ribbon5Bridge
variable {G K : Type*} [Group G] [Field K]

theorem decode_enc (w : List P) : decode (enc w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (⟨a.val % 3, _⟩ : P) :: decode (enc w) = _
    rw [ih]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem word_link (k : Count) (a : Nat) :
    block k a = (RibbonD3Field.chart k).ports.take a := by
  have H := (linked_all k).2.2
  change (RibbonD3Field.chart k).ports.map Fin.val = charts[k.val]!.ports.toList at H
  rw [getElem!_pos charts k.val (idx k).isLt] at H
  change enc (RibbonD3Field.chart k).ports = (mc k).ports.toList at H
  unfold block
  rw [←H]
  unfold enc
  rw [←List.map_take]
  exact decode_enc _

theorem actual_point (μ : G →* Kˣ) (τ : G → K) (co : RibbonStationaryChart.Aff μ τ)
    (x y : G) (tx : τ x = 0) (ty : τ y = 1) (k : Count) (a : Nat) :
    let v := vertex x y k a
    (v.1,μ v.2,τ v.2) =
      RibbonAffine.eRow (μ x) (μ y) (RibbonD3Field.raw (RibbonD3Field.chart k) a) := by
  have H := (linked_all k).2.1
  change (RibbonD3Field.chart k).start = charts[k.val]!.startSide at H
  rw [getElem!_pos charts k.val (idx k).isLt] at H
  change (RibbonD3Field.chart k).start = (mc k).startSide at H
  rw [(data_valid k).1] at H
  simpa [vertex,word_link,start,H] using
    RibbonD3Field.position_sound μ τ co x y tx ty (RibbonD3Field.chart k) a

theorem affine_collision (μ : G →* Kˣ) (τ : G → K) (co : RibbonStationaryChart.Aff μ τ)
    (x y : G) (tx : τ x = 0) (ty : τ y = 1) (k : Count) (a b : Nat)
    (h : vertex x y k a = vertex x y k b) :
    RibbonAffine.eRow (μ x) (μ y) (RibbonD3Field.raw (RibbonD3Field.chart k) a) =
      RibbonAffine.eRow (μ x) (μ y) (RibbonD3Field.raw (RibbonD3Field.chart k) b) := by
  rw [←actual_point μ τ co x y tx ty k a,←actual_point μ τ co x y tx ty k b,h]

#print axioms affine_collision
end RibbonD3FieldPoint
