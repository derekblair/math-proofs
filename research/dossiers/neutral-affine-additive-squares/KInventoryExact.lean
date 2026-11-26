import KInventory

namespace KInventoryExact
open KInventory KPhase KProjection

variable (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ)

def enumState : List (Q D k) :=
  (finPi (fun _ => enumZ D) : List (Fin (k+1+1) → FiniteTrip.Alpha D)).flatMap
      fun a => (finPi (fun _ => bitList) : List (Fin (k+1) → Bool)).map (fun b => (a,b))

theorem mem_state (s : Q D k) : s ∈ enumState D k := by
  apply List.mem_flatMap.mpr
  refine ⟨s.1,mem_finPi _ (fun _ => mem_enumZ D) _,?_⟩
  exact List.mem_map.mpr ⟨s.2,mem_finPi _ (fun _ => mem_bitList) _,Prod.eta _⟩

def enumCandidate : List (KFinite.Candidate D (k+1) f) :=
  (enumState D k).flatMap fun s =>
    (finPi (fun i => finList (f (s.1 i).val).length)).map (Sigma.mk s)

theorem mem_candidate (s : KFinite.Candidate D (k+1) f) : s ∈ enumCandidate D f k := by
  apply List.mem_flatMap.mpr
  refine ⟨s.1,mem_state D k _,?_⟩
  exact List.mem_map.mpr ⟨s.2,mem_finPi _ (fun _ => mem_finList) _,Sigma.eta _⟩

def enumEdge : List (E D f k) :=
  enumSub (enumCandidate D f k) (fun s => KFinite.edgeGuard f s.1 s.2)

theorem mem_edge (e : E D f k) : e ∈ enumEdge D f k :=
  mem_enumSub _ _ (fun s _ => mem_candidate D f k s) e

variable (B : ℤ)

def enumTail : List ((Fin k → PhaseFinite.Coord B) × Bool) :=
  (finPi (fun _ => enumZ (IntegerTrace.box B)) : List (Fin k → PhaseFinite.Coord B)).flatMap fun x =>
    bitList.map (Prod.mk x)

theorem mem_tail (t : (Fin k → PhaseFinite.Coord B) × Bool) : t ∈ enumTail k B := by
  apply List.mem_flatMap.mpr
  refine ⟨t.1,mem_finPi _ (fun _ => mem_enumZ _) _,?_⟩
  exact List.mem_map.mpr ⟨t.2,mem_bitList _,Prod.eta _⟩

def enumVertex : List (Vertex D k B) :=
  (enumState D k).flatMap fun s => (enumTail k B).map (Prod.mk s)

theorem mem_vertex (w : Vertex D k B) : w ∈ enumVertex D k B :=
  List.mem_flatMap.mpr ⟨w.1,mem_state D k _,List.mem_map.mpr ⟨w.2,mem_tail k B _,Prod.eta _⟩⟩

variable (v : ℤ × ℤ) (m : ℤ)

def enumArc : List (Arc D f k v m B) :=
  enumSub ((enumEdge D f k).flatMap fun e => (enumTail k B).map (Prod.mk e))
    (arcCondition v m B)

theorem mem_arc (t : Arc D f k v m B) : t ∈ enumArc D f k B v m := by
  apply mem_enumSub
  intro w _
  exact List.mem_flatMap.mpr ⟨w.1,mem_edge D f k _,List.mem_map.mpr ⟨w.2,mem_tail k B _,Prod.eta _⟩⟩

def absWeights : List ℕ :=
  (enumEdge D f k).flatMap fun e => (finList k).map fun j => (ex v j e).natAbs

def bound : ℤ := ((absWeights D f k v).foldr max (0 : ℕ) : ℕ)

theorem bound_nonneg : 0 ≤ bound D f k v := Int.natCast_nonneg _

theorem member_le_fold (L : List ℕ) (x : ℕ) (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem bound_covers (e : E D f k) (j : Fin k) : |ex v j e| ≤ bound D f k v := by
  have hm : (ex v j e).natAbs ∈ absWeights D f k v :=
    List.mem_flatMap.mpr ⟨e,mem_edge D f k e,List.mem_map.mpr ⟨j,mem_finList j,rfl⟩⟩
  have h := member_le_fold (absWeights D f k v) _ hm
  unfold bound
  rw [← Int.natCast_natAbs]
  exact Int.ofNat_le.mpr h

theorem bound_zero : 0 ∈ IntegerTrace.box (bound D f k v) :=
  by rw [IntegerTrace.box_iff,abs_zero]; exact bound_nonneg D f k v

end KInventoryExact

#print axioms KInventoryExact.mem_arc
#print axioms KInventoryExact.bound_covers
