import N62FourHubLocal

namespace Erdos151N62

/-- The order-62 ambient-degree-twelve, core-degree-ten, 17-edge
row saturates every global special-column and lone incidence budget. -/
theorem saturated_seventeen
    (I L A D : Nat)
    (outside : 135≤I+A+D) (inside : I+34≤132)
    (special : 2*(A+D)≤L+12) (lone : A+2*D≤L)
    (hl : L≤62) (single : A≤12) :
    I=98 ∧ L=62 ∧ A=12 ∧ D=25 := by omega

/-- There are exactly two noncore ambient owners. Saturating the
ten core slots and two other slots forces each latter total to 11. -/
theorem saturated_ghost_slots (totalCore g h : Nat)
    (core : totalCore≤40) (ga : g≤11) (hb : h≤11)
    (eq : totalCore+g+h=62) : totalCore=40 ∧ g=11 ∧ h=11 := by omega

/-- An owner of degree ten has only one nonneighbor. The number of
edges of the owner graph not internal to its neighborhood is at
most the edges incident to it or that one nonneighbor. Once each
owner has a marked leaf, all ten neighbor-leaf edges and the
opposite double columns are distinct forced lone attachments. -/
theorem saturated_pressure (inside otherDegree loneLeaf : Nat)
    (partition : 25≤10+otherDegree+inside) (other : otherDegree≤10)
    (forces : 1+10+inside≤loneLeaf) : 16≤loneLeaf := by omega

#print axioms saturated_seventeen
#print axioms saturated_pressure
end Erdos151N62
