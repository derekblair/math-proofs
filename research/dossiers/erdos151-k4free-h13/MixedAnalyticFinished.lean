import AnalyticTenTemplate
import N63SquarelessPetersen

namespace H13MixedComponents
open H13PetersenComponents
open Erdos151H12 Erdős151.Upper Erdos151CoreHigh Erdos151MarkedLinkTable

theorem moore_ten_verified : MooreTen := by
  intro D inst sym irr tf one deg
  exact Erdos151N63.squareless_cubic_petersen D (by simp) sym irr tf one deg

/-- Analytic non-Ramsey endpoint under the explicit Hall projection input.
No finite 10-link atlas, external SAT, or nonstandard axiom is needed. -/
theorem nonRamsey_of_neutral_shapes_with_hall {V : Type u} [Fintype V] [DecidableEq V]
    (C : V→V→Prop) [DecidableRel C]
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (tf : ∀ w a b c, C w a → C w b → C w c → C a b → C a c → ¬C b c)
    (size : Fintype.card V ≤ 63) (hall : HallProjection63.{u})
    (shapes : ∀ v, (neighbors C v).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) v, (edges L.kind).length=12) ∨
      ((neighbors C v).card=10 ∧ ∀ a∈neighbors C v,
        NineLinkPivot.deg C (neighbors C v) a=3)) :
    ¬ BikovLocal.Ramsey C :=
  nonRamsey_of_neutral_shapes C sym irr size hall shapes
    (actual_ten_template moore_ten_verified C sym irr tf)

#print axioms nonRamsey_of_neutral_shapes_with_hall
end H13MixedComponents
