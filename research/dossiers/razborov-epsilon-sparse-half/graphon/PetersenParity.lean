import TripleNonorthogonal

namespace SparseHalfCountableEndpoint.PetersenParity

/-- The four A vertices carry the occupied even signatures in order
000,011,101,110. The last six are the two choices of each of three blocks. -/
def bit (i : Fin 4) (k : Fin 3) : Bool :=
  (![![false,false,false], ![false,true,true], ![true,false,true], ![true,true,false]] :
    Fin 4 → Fin 3 → Bool) i k

def sideLabel (i : Fin 10) : Fin 3 × Bool := (⟨(i.val-4)/2 % 3,Nat.mod_lt _ (by decide)⟩,
  (i.val-4)%2 == 1)

def adjacent (i j : Fin 10) : Bool :=
  if hi : i.val<4 then
    if j.val<4 then false else bit ⟨i.val,hi⟩ (sideLabel j).1 == (sideLabel j).2
  else
    if hj : j.val<4 then bit ⟨j.val,hj⟩ (sideLabel i).1 == (sideLabel i).2
    else ((sideLabel i).1==(sideLabel j).1) && ((sideLabel i).2!=(sideLabel j).2)

/-- Isomorphism labels into the Kneser description KG(5,2). -/
def label (i : Fin 10) : Finset (Fin 5) :=
  (![ {0,1}, {0,2}, {0,3}, {0,4}, {3,4},
      {1,2}, {2,4}, {1,3}, {2,3}, {1,4} ] : Fin 10 → Finset (Fin 5)) i

theorem label_size : ∀ i : Fin 10, (label i).card=2 := by decide

theorem label_inj : Function.Injective label := by
  change ∀ a b : Fin 10, label a=label b → a=b
  decide

theorem label_surj : ∀ s : Finset (Fin 5), s.card=2 → ∃ i : Fin 10,label i=s := by decide

theorem kneser_adjacency :
    ∀ i j : Fin 10, adjacent i j=true ↔ Disjoint (label i) (label j) := by decide

/-- A compact family of five-cell tight halves covers every template
edge. For completed model, each has exactly two unordered edges. -/
def tightHalves : List (Finset (Fin 10)) :=
  [{0,1,2,3,4},{0,1,2,3,5},{0,1,2,3,6},{0,1,2,3,7},
    {0,1,2,3,8},{0,1,2,3,9},{0,4,5,7,9},{4,6,7,8,9}]

def orderedEdges (s : Finset (Fin 10)) : Nat :=
  ((s ×ˢ s).filter fun z => adjacent z.1 z.2 = true).card

theorem tight_five :
    ∀ s ∈ tightHalves, s.card=5 ∧ orderedEdges s=4 := by
  intro s h
  simp only [tightHalves,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem each_edge_seen : ∀ i j : Fin 10, adjacent i j=true →
    ∃ s ∈ tightHalves, i∈s ∧ j∈s := by decide

#print axioms label_surj
#print axioms tight_five
#print axioms each_edge_seen
#print axioms kneser_adjacency
end SparseHalfCountableEndpoint.PetersenParity
