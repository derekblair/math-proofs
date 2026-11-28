import LargePoolTen
import CoreDensityAverage
import WagnerCoreImpossible
import H12WagnerAdapter
import H12MaximalCliqueAdapter
import RamseySeed53

open scoped BigOperators
namespace Erdős151.H12

open Erdos151H12 Erdos151CoreHigh

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Transport form of Bikov's exact finite atlas. This is a theorem
parameter until the independent Fin8 coverage replay is assembled. -/
def DegreeEightAtlas (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (C : V → V → Prop) [DecidableRel C],
    BikovLocal.Sym C → BikovLocal.Loopless C → BikovLocal.TriangleFreeLinks C →
    BikovLocal.Ramsey C →
    (∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H) →
    ∀ w, (neighbors C w).card=8 →
      Nonempty (NamedLink (neighbors C) (ambientCodeg C) w)

theorem ramsey_has_free_twelve_of_atlas (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (atlas : DegreeEightAtlas V)
    (n53 : 53 ≤ Fintype.card V) (ramsey : BikovLocal.Ramsey G) :
    ∃ S : Finset V, 12 ≤ S.card ∧ Free (Forbidden G) (S : Set V) := by
  classical
  by_contra! bad
  have upper : FreeCap G 11 := by
    intro T hT
    by_contra h
    exact bad T (by omega) hT
  have deg (w : V) : (neighbors G w).card≤11 := by
    apply upper
    have eq : (↑(neighbors G w) : Set V) = {u | G w u} := by ext u; simp [neighbors]
    rw [eq]
    exact neighborhood_free G sym link w
  obtain ⟨C,sub,cs,ci,ct,cr,nonempty,minC,two,minimal⟩ :=
    BikovLocal.extract_core_minimal G (fun {_ _} h=>sym h) irr
      (fun w a b c wa wb wc ab ac bc=>link w a b c wa wb wc ab bc ac) ramsey
  let J := asSimple C (fun {_ _} h=>cs h) ci
  let edgecount (w : V) := ((J.cliqueFinset 3).filter (fun t=>w∈t)).card
  have eqn (w : V) : neighbors C w=Upper.nbr J.Adj w := rfl
  have he (w : V) : (∑ x ∈ neighbors C w, Upper.row C (neighbors C w) x)=2*edgecount w := by
    exact directed_link_sum J w
  have mC {a b : V} (ab : C a b) : 8 ≤ (neighbors C a).card := by
    have h := minC a ⟨b,ab⟩
    simpa only [Fintype.card_subtype,neighbors] using h
  have twoC : TwoTriangles C := by
    intro u v uv
    obtain ⟨a,b,ne,ha,hb⟩ := two u v uv
    exact ⟨a,b,ne,ha.1,ha.2,hb.1,hb.2⟩
  have scope := atlas C cs ci ct cr minimal
  have loc := unified_contributions_from_named_atlas C G sym irr link
    (fun {_ _} h=>cs h) (fun {_ _} h=>sub h) twoC deg mC upper
    (fun T h=>large_pool_free_ten (G := G) sym irr link R41 T h) scope n53 edgecount he
  have dn (w : V) (hw : (Upper.nbr J.Adj w).Nonempty) : 8 ≤ (Upper.nbr J.Adj w).card := by
    obtain ⟨u,hu⟩ := hw
    rw [←eqn]
    exact mC (Finset.mem_filter.mp hu).2
  have tight := actual_density_forces_twelve J cr minimal dn (fun w hw => loc w (dn w hw))
  have atlas12 (w : V) (hw : (neighbors C w).Nonempty) :
      ∃ L : NamedLink (neighbors C) (ambientCodeg C) w,
        (Erdos151MarkedLinkTable.edges L.kind).length=12 := by
    have hh := tight w hw
    obtain ⟨L⟩ := scope w hh.1
    exact ⟨L,row12_chart C w L hh.2⟩
  have wi (w : V) (hw : ∃ v,C w v) :
      ∃ e : Fin 8 ≃ {x : V // x≠w ∧ C w x},
        ∀ i j, WagnerFin8.Adj i j ↔ C (e i).val (e j).val := by
    obtain ⟨v,hv⟩ := hw
    exact wagner_iso_after_density C (fun {_ _} h=>cs h) ci atlas12 w
      ⟨v,(mem_neighbors C).mpr hv⟩
  exact minimal_locally_wagner_impossible C cs ci cr minimal nonempty wi

theorem erdos151_k4free_H12_of_atlas (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (atlas : DegreeEightAtlas V) (H : TriangleIndependentAtLeast 12 V) :
    ∃ T : Finset V, T.card ≤ Fintype.card V-12 ∧
      ∀ C, MaximalNontrivialClique G C → ∃ x ∈ C, x∈T := by
  have n : 52 < Fintype.card V := by
    obtain ⟨Q,qs,qi,qt,qc⟩ := Erdos151Ramsey.Seed53.ramsey312_ge53
    exact triangle_independence_forces_large_of_witness 12 52 H ⟨Q,qs,qi,qt,fun S h => Nat.lt_succ_of_le (qc S h)⟩
  exact k4free_transversal_from_ramsey_case G 12 sym irr link H
    (ramsey_has_free_twelve_of_atlas G sym irr link R41 atlas (by omega))

#print axioms erdos151_k4free_H12_of_atlas
end Erdős151.H12
