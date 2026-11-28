import N63MinimalCore

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12 Erdos151CoreHigh Erdős151.H12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

/-- Outputs exactly the order-eight or cubic order-ten local structure
for the remaining coloring lemma. The only local premise not discharged
here is the geometric exclusion of a noncubic dense ten-link. -/
theorem order63_tight_core
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : BikovLocal.Sub C G) (cs : BikovLocal.Sym C) (ci : BikovLocal.Loopless C)
    (ct : BikovLocal.TriangleFreeLinks C) (cr : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (coreMin : ∀ v, (neighbors C v).Nonempty → 8 ≤ (neighbors C v).card)
    (two : TwoTriangles C)
    (max12 : ∀ v, (neighbors G v).card ≤12) (size63 : 63 ≤ Fintype.card V)
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V))
    (noncubic : ∀ v, (neighbors C v).card=10 →
      30 ≤ (∑ a ∈ neighbors C v, deg G (neighbors C v) a) →
      (∃ a ∈ neighbors C v, 4 ≤ deg G (neighbors C v) a) → False) :
    ∀ v, (neighbors C v).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) v,
          (Erdos151MarkedLinkTable.edges L.kind).length=12) ∨
      ((neighbors C v).card=10 ∧ (neighbors G v).card=12 ∧
        ∀ a ∈ neighbors C v, deg C (neighbors C v) a=3) := by
  let S (v : V) := neighbors C v
  let d (v : V) := (S v).card
  let e (v : V) := ∑ a ∈ S v, deg C (S v) a
  have dpos (v : V) (hv : 0<d v) : 8≤d v := coreMin v (Finset.card_pos.mp hv)
  have min8 (v : V) (u : V) (hu : u∈S v) : 8≤d u := coreMin u
    ⟨v,(mem_neighbors C).mpr (cs ((mem_neighbors C).mp hu))⟩
  have rowMono (v a : V) : deg C (S v) a ≤ deg G (S v) a := by
    exact Finset.card_le_card (fun z hz => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1,sub (Finset.mem_filter.mp hz).2⟩)
  have m2 (v a : V) (h : a∈S v) : 2≤deg C (S v) a := by
    obtain ⟨x,y,neq,vx,ax,vy,ay⟩ := two v a ((mem_neighbors C).mp h)
    exact Finset.one_lt_card.mpr ⟨x,Finset.mem_filter.mpr ⟨(mem_neighbors C).mpr vx,ax⟩,
      y,Finset.mem_filter.mpr ⟨(mem_neighbors C).mpr vy,ay⟩,neq⟩
  have nL (a b : V) (ab : C a b) : ¬Lone G a b := by
    obtain ⟨x,y,ne,ax,bx,ay,byy⟩ := two a b ab
    exact fun h => h.2 x ⟨sub ax,sub bx⟩
  have up (P : Finset V) (f : Free (Forbidden G) (P : Set V)) : P.card≤12 := by
    by_contra! h
    exact noFree ⟨P,by omega,f⟩
  have monoD (v : V) : d v ≤ (neighbors G v).card :=
    Finset.card_le_card (fun a ha => (mem_neighbors G).mpr (sub ((mem_neighbors C).mp ha)))
  have atlas := H12.verified_degree_eight_atlas (V:=V) C cs ci ct cr minimal
  have parity (v : V) : ∃ m, e v=2*m := Erdos151Ramsey.even_degree_sum C (S v) (fun {_ _} h=>cs h) ci
  have cap8 (v : V) (hv : d v=8) : e v≤24 := by
    obtain ⟨L⟩ := atlas v hv
    obtain ⟨m,hm⟩ := parity v
    have b := (named_link_bounds C v m hm L).1.2
    omega
  have cap10 (v : V) (hv : d v=10) : e v≤30 := by
    by_cases dens : e v≤30
    · exact dens
    have mono : e v ≤ ∑ a ∈ S v, deg G (S v) a := Finset.sum_le_sum (fun a _ => rowMono v a)
    by_cases large : ∃ a ∈ S v, 4 ≤ deg G (S v) a
    · exact False.elim (noncubic v hv (by change 30 ≤ ∑ a ∈ S v, deg G (S v) a; omega) large)
    · push Not at large
      have h : (∑ a ∈ S v, deg G (S v) a) ≤ 3*d v := by
        simpa [d,Nat.mul_comm] using (Finset.sum_le_sum (s:=S v) (g:=fun _ => 3) (fun a ha =>
          (Nat.lt_succ_iff.mp (large a ha))))
      omega
  have cap11 (v : V) (hv : d v=11) : e v≤28 := by
    have mn := monoD v
    have mx := max12 v
    obtain ⟨m,hm⟩ := parity v
    by_cases h11 : (neighbors G v).card=11
    · have h := degreeEleven_at_least63_h13 G C sym irr link (fun {_ _} h=>sub h) two max12 up size63 v h11 (min8 v) m hm hv
      omega
    · have h12 : (neighbors G v).card=12 := by omega
      have h := (degreeTwelve_at_least63_h13 G C sym irr link (fun {_ _} h=>sub h) two max12 up size63 v h12 (min8 v) m hm).2.1 hv
      omega
  have cap12 (v : V) (hv : d v=12) : e v≤24 := by
    have mn := monoD v
    have mx := max12 v
    obtain ⟨m,hm⟩ := parity v
    have h12 : (neighbors G v).card=12 := by omega
    have h := (degreeTwelve_at_least63_h13 G C sym irr link (fun {_ _} h=>sub h) two max12 up size63 v h12 (min8 v) m hm).2.2 hv
    omega
  have noBi (v : V) (dv : d v=10) : ¬TwoChargedPivots.Bicuts C (S v) :=
    no_bipartite_at_core_vertex C cs ci cr minimal v (Finset.card_pos.mp (by change 0<d v; omega))
  have tight (v : V) : e v=3*d v :=
    actual_neutral_by_routing G C sym irr link R41 (fun _ _ h=>sub h) (fun {_ _} h=>cs h) nL ci dpos m2 max12 size63
      cap8 cap10 cap11 cap12 noBi noFree (minimal_core_global_score C cs ci cr minimal) v
  intro v hv
  have minD := coreMin v hv
  change 8≤d v at minD
  have maxD := max12 v
  have md := monoD v
  have t := tight v
  have r : d v=8 ∨ d v=10 := by
    by_contra! h
    have casesD : d v=9 ∨ d v=11 ∨ d v=12 := by omega
    rcases casesD with h9|h11|h12
    · obtain ⟨m,hm⟩ := parity v
      omega
    · have := cap11 v h11
      omega
    · have := cap12 v h12
      omega
  rcases r with r8|r10
  · obtain ⟨L⟩ := atlas v r8
    exact Or.inl ⟨L,row12_chart C v L (by omega : e v=24)⟩
  · have sum : e v ≤ ∑ a ∈ S v, deg G (S v) a := Finset.sum_le_sum (fun a _ => rowMono v a)
    have large : ¬ ∃ a∈S v, 4≤deg G (S v) a := noncubic v r10 (by change 30 ≤ ∑ a ∈ S v, deg G (S v) a; omega)
    push Not at large
    have high3 (a : V) (ha : a∈S v) : deg G (S v) a≤3 := Nat.lt_succ_iff.mp (large a ha)
    have per (a : V) (ha : a∈S v) : deg C (S v) a≤3 := (rowMono v a).trans (high3 a ha)
    have eq : (∑ a ∈ S v, deg C (S v) a) = ∑ _a ∈ S v,(3:ℕ) := by
      change e v=_
      simp [d, S, Nat.mul_comm] at t ⊢
      exact t
    have cubic (a : V) (ha : a∈S v) : deg C (S v) a=3 := (Finset.sum_eq_sum_iff_of_le per).mp eq a ha
    have ac (a : V) (ha : a∈S v) : deg G (S v) a=3 := by
      have := cubic a ha
      have := rowMono v a
      have := high3 a ha
      omega
    have d12 : (neighbors G v).card=12 := by
      by_contra! h
      exact noFree (low_ambient_cubic_ten_free13 G C sym irr link R41 (fun _ _ h=>sub h) (fun {_ _} h=>cs h) nL v r10
        (by omega) ac (min8 v) max12 size63)
    exact Or.inr ⟨r10,d12,cubic⟩

#print axioms order63_tight_core
end Erdos151H13
