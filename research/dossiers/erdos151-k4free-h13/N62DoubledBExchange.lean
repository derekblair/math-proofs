import N62DoubleStar

namespace Erdos151N62
open Erdős151 Erdos151H12 Erdos151H13
variable {V : Type*} [Fintype V] [DecidableEq V] (G : V→V→Prop) [DecidableRel G]

/-- Two B columns on an adjacent owner pair cannot coexist with
two double columns from that pair to a common third owner. -/
theorem doubledB_no_common_double
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a)
    (tf : TriangleFreeLinks G)
    (S : Finset V) (sc : S.card=12)
    (sf : Free (Forbidden G) (S : Set V))
    (upper : ∀ L : Finset V, Free (Forbidden G) (L : Set V) → L.card≤12)
    (u v g x y a b : V)
    (us : u∈S) (vs : v∈S) (gs : g∈S)
    (xy : x≠y) (xa : x≠a) (xb : x≠b) (ya : y≠a) (yb : y≠b) (ab : a≠b)
    (xn : x∉S) (yn : y∉S) (an : a∉S) (bn : b∉S)
    (uv : G u v) (ux : G u x) (vx : G v x) (uy : G u y) (vy : G v y)
    (ga : Lone G g a) (gb : Lone G g b) (ua : Lone G u a) (vb : Lone G v b)
    (xs : support G S x⊆{u,v}) (ys : support G S y⊆{u,v})
    (asup : support G S a⊆{g,u}) (bsup : support G S b⊆{g,v}) : False := by
  let Z : Finset V := {x,y,a,b}
  let P : Finset V := {g,u,v}
  have pc : P.card≤3 := by
    have h1 := Finset.card_insert_le g ({u,v}:Finset V)
    have h2 := Finset.card_insert_le u ({v}:Finset V)
    rw [Finset.card_singleton] at h2
    change P.card ≤ ({u,v}:Finset V).card+1 at h1
    omega
  have zc : Z.card=4 := by
    simp [Z, Finset.card_insert_of_notMem, xy,xa,xb,ya,yb,ab]
  have crossXY : ¬G x y := fun h => tf u v x y uv ux uy vx h vy
  have indep : ∀ p∈Z, ∀ q∈Z, ¬G p q := by
    simp only [Z,Finset.mem_insert,Finset.mem_singleton]
    rintro p (rfl|rfl|rfl|rfl) q (rfl|rfl|rfl|rfl)
    all_goals first
    | exact irr _
    | exact crossXY
    | exact fun h => crossXY (sym h)
    | exact lone_neighbors_nonadjacent G sym ga gb.1
    | exact lone_neighbors_nonadjacent G sym gb ga.1
    | exact lone_neighbors_nonadjacent G sym ua ux
    | exact lone_neighbors_nonadjacent G sym ua uy
    | exact lone_neighbors_nonadjacent G sym vb vx
    | exact lone_neighbors_nonadjacent G sym vb vy
    | exact fun h => lone_neighbors_nonadjacent G sym ua ux (sym h)
    | exact fun h => lone_neighbors_nonadjacent G sym ua uy (sym h)
    | exact fun h => lone_neighbors_nonadjacent G sym vb vx (sym h)
    | exact fun h => lone_neighbors_nonadjacent G sym vb vy (sym h)
  have out : Disjoint S Z := by
    apply Finset.disjoint_left.mpr
    intro a ha hz
    simp only [Z,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl
    exacts [xn ha,yn ha,an ha,bn ha]
  have psub : P⊆S := by simp [P,Finset.insert_subset_iff, gs,us,vs]
  have supp : ∀ p∈Z, support G S p⊆P := by
    intro a hz
    simp only [Z,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact xs.trans (by simp [P,Finset.insert_subset_iff])
    · exact ys.trans (by simp [P,Finset.insert_subset_iff])
    · exact asup.trans (by simp [P,Finset.insert_subset_iff])
    · exact bsup.trans (by simp [P,Finset.insert_subset_iff])
  have le := independent_supported_count G sym irr S P Z sc psub sf upper out indep supp
  omega

#print axioms doubledB_no_common_double
end Erdos151N62
