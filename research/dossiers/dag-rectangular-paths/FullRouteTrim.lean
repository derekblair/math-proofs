import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

namespace SparseDAG.RouteTrim

variable {V E R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
variable (u v : E → V) (w : E → R)

inductive Route : V → List E → V → Prop where
  | nil (s : V) : Route s [] s
  | cons (e : E) {P : List E} {t : V} :
      Route (v e) P t → Route (u e) (e :: P) t

theorem append_route {s t z : V} {P Q : List E}
    (hP : Route u v s P t) (hQ : Route u v t Q z) :
    Route u v s (P ++ Q) z := by
  induction hP with
  | nil => exact hQ
  | cons e _ ih => exact Route.cons e (ih hQ)

theorem split_route {s t : V} {P Q : List E} {e : E}
    (h : Route u v s (P ++ e :: Q) t) :
    Route u v s P (u e) ∧ Route u v (v e) Q t := by
  induction P generalizing s with
  | nil =>
    cases h with
    | cons _ H => exact ⟨Route.nil _, H⟩
  | cons a P ih =>
    cases h with
    | cons _ H =>
      obtain ⟨hL, hR⟩ := ih H
      exact ⟨Route.cons a hL, hR⟩

theorem rank_tail (rank : V → Nat) (inc : ∀ e, rank (u e) < rank (v e))
    {s t : V} {P : List E} (p : Route u v s P t) :
    ∀ x ∈ P.map v, rank s < rank x := by
  induction p with
  | nil => simp
  | cons e _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact inc e
    · exact Nat.lt_trans (inc e) (ih x hx)

theorem topological_route_simple (rank : V → Nat)
    (inc : ∀ e, rank (u e) < rank (v e)) {s t : V} {P : List E}
    (p : Route u v s P t) : (s :: P.map v).Nodup := by
  have fresh : s ∉ P.map v := fun hs => (Nat.lt_irrefl _ (rank_tail u v rank inc p s hs))
  apply List.nodup_cons.mpr
  refine ⟨fresh, ?_⟩
  induction p with
  | nil => simp
  | cons e p ih =>
    apply List.nodup_cons.mpr
    have X : v e ∉ List.map v _ := fun hs => Nat.lt_irrefl _ (rank_tail u v rank inc p (v e) hs)
    exact ⟨X, ih X⟩

def Minimum (s t : V) (d : R) : Prop :=
  (∃ P, Route u v s P t ∧ (P.map w).sum = d) ∧
  ∀ P, Route u v s P t → d ≤ (P.map w).sum

theorem edge_test {s t : V} {e : E} {a b d : R}
    (hA : Minimum u v w s (u e) a)
    (hB : Minimum u v w (v e) t b)
    (hD : Minimum u v w s t d) :
    a + w e + b = d ↔
    ∃ P, Route u v s P t ∧ (P.map w).sum = d ∧ e ∈ P := by
  constructor
  · intro he
    obtain ⟨P, p, hp⟩ := hA.1
    obtain ⟨Q, q, hq⟩ := hB.1
    refine ⟨P ++ e :: Q, append_route u v p (Route.cons e q), ?_, by simp⟩
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hp, hq]
    rwa [← add_assoc]
  · rintro ⟨L, hL, hcost, he⟩
    obtain ⟨P, Q, rfl⟩ := List.append_of_mem he
    obtain ⟨p, q⟩ := split_route u v hL
    have la := hA.2 P p
    have lb := hB.2 Q q
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hcost
    apply le_antisymm
    · calc
        a + w e + b ≤ (P.map w).sum + w e + (Q.map w).sum :=
          add_le_add (add_le_add_left la _) lb
        _ = d := by rwa [add_assoc]
    · obtain ⟨P', p', hp'⟩ := hA.1
      obtain ⟨Q', q', hq'⟩ := hB.1
      have hd := hD.2 _ (append_route u v p' (Route.cons e q'))
      simpa only [List.map_append, List.map_cons, List.sum_append, List.sum_cons,
        hp', hq', add_assoc] using hd

omit [LinearOrder R] [IsOrderedAddMonoid R] in
/-- Restrict allowed edges to a union containing each required minimum
route. It cannot introduce a route; every required minimum route remains. -/
theorem union_preserves {I : Type*}
    (s t : I → V) (d : I → R) (i : I) (P : List E) :
    (Route u v (s i) P (t i) ∧ (P.map w).sum = d i) ↔
    (Route u v (s i) P (t i) ∧ (P.map w).sum = d i ∧
      ∀ e ∈ P, ∃ j Q, Route u v (s j) Q (t j) ∧ (Q.map w).sum = d j ∧ e ∈ Q) := by
  constructor
  · rintro ⟨hp, hw⟩
    exact ⟨hp, hw, fun e he => ⟨i,P,hp,hw,he⟩⟩
  · exact fun h => ⟨h.1,h.2.1⟩

#print axioms topological_route_simple
#print axioms edge_test
#print axioms union_preserves
end SparseDAG.RouteTrim
