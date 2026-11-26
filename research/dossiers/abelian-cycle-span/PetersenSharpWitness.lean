import PetersenSharpCover

namespace PetersenSharp

/-- A simple cycle in the actual lifted graph, with its seam edge included. -/
def LiftCycle (n : ℕ) : Prop :=
  ∃ v : Fin n → V, Function.Injective v ∧
    ∀ i : Fin n, edge (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)


private def cycle : Fin 16 → V := ![(0,0),(1,0),(2,0),(3,0),(8,1),(6,4),(1,4),(0,4),(5,4),(8,4),(3,3),(2,3),(1,3),(6,3),(8,0),(5,0)]

theorem cycle16 : LiftCycle 16 := by
  refine ⟨cycle,?_,?_⟩
  · decide
  · decide

private def walk : V → List P → V
  | u, [] => u
  | u, p::ps => walk (next u p) ps

private def paths : B → Fin 5 → List P := ![
  ![[],[1,1,2,0,2],[0,2,0,0,2],[0,2,1,2,0],[2,0,0,2,0]],
  ![[0],[1,2,1,2,1],[1,2,0,2],[2,1,1,2],[1,1,2,1,2]],
  ![[0,0],[1,2,1,2],[1,2,0,2,0],[2,1,1,2,0],[2,1,2,1]],
  ![[1,1],[0,2,0,2],[1,2,0,2,0,0],[0,2,1,2,1],[2,1,2]],
  ![[1],[0,2,0,2,0],[0,2,0,0,2,1],[0,2,1,2],[2,0,0,2]],
  ![[2],[1,1,2,0],[0,2,0,0],[0,2,1,2,0,2],[0,2,1,1,1]],
  ![[0,2],[2,0,0,0],[1,2,0],[2,1,1],[1,1,2,1]],
  ![[2,0],[1,2,1],[0,2,0,0,0],[1,1,2,1,1,1],[0,2,1,1]],
  ![[2,1],[1,1,2],[0,2,0],[2,0,0,0,0],[1,2,0,0]],
  ![[1,2],[2,1,1,1],[1,1,2,1,1],[0,2,1],[2,0,0]]
]

def start : V := (0,0)

private def rootPath (u : V) : List P := paths u.1 ⟨u.2.val,ZMod.val_lt u.2⟩

private theorem path_ok (u : V) : walk start (rootPath u) = u := by decide +revert

abbrev Reaches := Relation.ReflTransGen edge

private theorem walk_ok (u : V) (ps : List P) : Reaches u (walk u ps) := by
  induction ps generalizing u with
  | nil => exact .refl
  | cons p ps ih => exact (Relation.ReflTransGen.single ⟨p,rfl⟩).trans (ih _)

theorem root_connected (u : V) : Reaches start u := by
  simpa only [path_ok] using walk_ok start (rootPath u)

theorem connected (u v : V) : Reaches u v := by
  have h := root_connected u
  have r : Reaches u start := by
    induction h with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single (edge_symm e)).trans ih
  exact r.trans (root_connected v)

end PetersenSharp

#print axioms PetersenSharp.cycle16
#print axioms PetersenSharp.connected
