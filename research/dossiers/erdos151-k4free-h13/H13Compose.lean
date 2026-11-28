import HubFinishNine
import H12Final

open scoped BigOperators
namespace Erdős151.H13
open Erdos151H12 Erdos151H13 Erdos151CoreHigh Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Explicit interface for the remaining high-degree local row proof. -/
def HighCoreStrict (G : V → V → Prop) : Prop :=
  ∀ (C : V → V → Prop) [DecidableRel C],
    BikovLocal.Sub C G → BikovLocal.Sym C → BikovLocal.Loopless C →
    TwoTriangles C →
    (∀ a b, C a b → 8 ≤ (neighbors C a).card) →
    ∀ w, 10 ≤ (neighbors C w).card →
      (∑ v ∈ neighbors C w, NineLinkPivot.deg C (neighbors C w) v) <
        3 * (neighbors C w).card

/-- Assembly for the order-at-least-64 regime; combines the proved nine-hub
step with the earlier marked atlas and Wagner core exclusion. The
high-degree local bound still enters this assembly as a named premise. -/
theorem ramsey_free13_of_high_core_strict (G : V → V → Prop)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → H10.TriangleIndependentTen (Fin n))
    (n64 : 64 ≤ Fintype.card V) (ramsey : BikovLocal.Ramsey G)
    (high : (¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) → HighCoreStrict G) :
    ∃ S : Finset V, 13 ≤ S.card ∧ Free (Forbidden G) (S : Set V) := by
  classical
  by_contra bad
  have deg (w : V) : (neighbors G w).card ≤ 12 := by
    by_contra hn
    have eq : (↑(neighbors G w) : Set V) = {u | G w u} := by
      ext u
      simp [neighbors]
    exact bad ⟨neighbors G w,by omega,by rw [eq]; exact neighborhood_free G sym link w⟩
  obtain ⟨C,sub,cs,ci,ct,cr,nonempty,minC,two,minimal⟩ :=
    BikovLocal.extract_core_minimal G (fun {_ _} h=>sym h) irr
      (fun w a b c wa wb wc ab ac bc=>link w a b c wa wb wc ab bc ac) ramsey
  let J := asSimple C (fun {_ _} h=>cs h) ci
  let ed (w : V) := ((J.cliqueFinset 3).filter (fun t=>w∈t)).card
  have he (w : V) : (∑ x ∈ neighbors C w, Upper.row C (neighbors C w) x)=2*ed w := by
    exact directed_link_sum J w
  have mC {a b : V} (ab : C a b) : 8 ≤ (neighbors C a).card := by
    have h := minC a ⟨b,ab⟩
    simpa only [Fintype.card_subtype,neighbors] using h
  have twoC : TwoTriangles C := by
    intro u v uv
    obtain ⟨a,b,ne,ha,hb⟩ := two u v uv
    exact ⟨a,b,ne,ha.1,ha.2,hb.1,hb.2⟩
  have nL (a b : V) (ab : C a b) : ¬ Lone G a b := by
    obtain ⟨c,d,neq,ac,bc,ad,bd⟩ := twoC a b ab
    exact fun h => h.2 c ⟨sub ac,sub bc⟩
  have scope := H12.verified_degree_eight_atlas (V := V) C cs ci ct cr minimal
  have loc (w : V) (hw : (neighbors C w).Nonempty) :
      2*ed w ≤ 3*(neighbors C w).card ∧ (9 ≤ (neighbors C w).card → 2*ed w < 3*(neighbors C w).card) := by
    have dw : 8 ≤ (neighbors C w).card := by
      obtain ⟨a,ha⟩ := hw
      exact mC ((mem_neighbors C).mp ha)
    by_cases r8 : (neighbors C w).card=8
    · obtain ⟨L⟩ := scope w r8
      have e := (named_link_bounds C w (ed w) (he w) L).1.2
      omega
    by_cases r9 : (neighbors C w).card=9
    · have e : ed w ≤ 13 := by
        by_contra h
        have dense : 28 ≤ ∑ a∈neighbors C w,NineLinkPivot.deg C (neighbors C w) a := by
          change 28 ≤ ∑ a∈neighbors C w,Upper.row C (neighbors C w) a
          rw [he w]
          omega
        exact bad (dense_core_nine_free13 G C sym irr link R41 (fun _ _ h => sub h)
          (fun {_ _} h => cs h) nL w r9 (fun _ h => mC (cs h)) deg n64 dense)
      omega
    have rh : 10 ≤ (neighbors C w).card := by omega
    have h := high bad C sub cs ci twoC (fun _ _ h => mC h) w rh
    change (∑ a∈neighbors C w,Upper.row C (neighbors C w) a) < _ at h
    rw [he w] at h
    omega
  have dn (w : V) (hw : (Upper.nbr J.Adj w).Nonempty) : 8 ≤ (Upper.nbr J.Adj w).card := by
    obtain ⟨u,hu⟩ := hw
    exact mC (Finset.mem_filter.mp hu).2
  have tight := actual_density_forces_twelve J cr minimal dn loc
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

#print axioms ramsey_free13_of_high_core_strict
end Erdős151.H13
