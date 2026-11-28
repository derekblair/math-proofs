import N63CoreCertified
import NeutralHostColor

namespace Erdős151.H13
open Finset
open scoped BigOperators
open Erdos151H12 Erdos151H13 Erdos151CoreHigh
open H13MixedComponents H13PetersenComponents

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The remaining finite local-template obligation, formulated for
arbitrary cubic triangle-free ten-links on the actual core. -/
def TenTemplateObligation : Prop :=
  ∀ (C : V → V → Prop) [DecidableRel C] (cs : BikovLocal.Sym C) (ci : BikovLocal.Loopless C),
    BikovLocal.TriangleFreeLinks C →
    ∀ w, (neighbors C w).card=10 →
    (∀ a∈neighbors C w, NineLinkPivot.deg C (neighbors C w) a=3) →
    HasTemplate (graphOf C cs ci) w

theorem ramsey_free13_order63_of_ten_templates (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : Fintype.card V=63) (hall : HallProjection63.{u})
    (local10 : TenTemplateObligation (V:=V))
    (ramsey : BikovLocal.Ramsey G) :
    ∃ T : Finset V, 13≤T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  by_contra bad
  have deg (w : V) : (neighbors G w).card ≤ 12 := by
    by_contra hn
    have eq : (↑(neighbors G w) : Set V) = {u | G w u} := by
      ext u
      simp [neighbors]
    exact bad ⟨neighbors G w,by omega,by rw [eq]; exact neighborhood_free G sym link w⟩
  obtain ⟨C,sub,cs,ci,ct,cr,_,minC,two,minimal⟩ :=
    BikovLocal.extract_core_minimal G (fun {_ _} h=>sym h) irr
      (fun w a b c wa wb wc ab ac bc=>link w a b c wa wb wc ab bc ac) ramsey
  have min8 (w : V) (hw : (neighbors C w).Nonempty) : 8 ≤ (neighbors C w).card := by
    obtain ⟨v,hv⟩ := hw
    have h := minC w ⟨v,(mem_neighbors C).mp hv⟩
    simpa only [Fintype.card_subtype,neighbors] using h
  have twoC : TwoTriangles C := by
    intro u v uv
    obtain ⟨a,b,ne,ha,hb⟩ := two u v uv
    exact ⟨a,b,ne,ha.1,ha.2,hb.1,hb.2⟩
  have shapes := certified_tight_core63 G C sym irr link R41 sub cs ci ct cr minimal min8 twoC deg n63.ge bad
  apply nonRamsey_of_neutral_shapes C cs ci n63.le hall _ _ cr
  · intro w hw
    rcases shapes w hw with h|⟨r,_,d⟩
    · exact Or.inl h
    · exact Or.inr ⟨r,d⟩
  · exact local10 C cs ci ct

/-- Order exactly 63; the finite template theorem is kept separate so
the final statement can be read with its actual external inputs. -/
theorem erdos151_k4free_H13_order63_of_ten_templates (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41≤n → H10.TriangleIndependentTen (Fin n))
    (n63 : Fintype.card V=63) (hall : HallProjection63.{u})
    (local10 : TenTemplateObligation (V:=V))
    (H : TriangleIndependentAtLeast 13 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-13 ∧
      ∀ Q, MaximalNontrivialClique G Q → ∃ x∈Q, x∈T :=
  k4free_transversal_from_ramsey_case G 13 sym irr link H
    (ramsey_free13_order63_of_ten_templates G sym irr link R41 n63 hall local10)

#print axioms erdos151_k4free_H13_order63_of_ten_templates
end Erdős151.H13
