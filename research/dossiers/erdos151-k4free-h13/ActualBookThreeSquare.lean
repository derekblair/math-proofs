import GenericHostSquare
import ActualCoTriangle

open scoped BigOperators
namespace Erdős151.H13
open Erdős151.H12 Erdős151.H12.Wagner
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A general square-bearing book-three coloring theorem. The link
conditions may hold for different finite link types at different vertices;
there is no classification or assumption that any specific link is Wagner. -/
theorem actual_book_three_square_safe (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : ∀ a b : V, Relation.ReflTransGen G.Adj a b)
    (linkConn : LinkDeletionConnected G)
    (cut : ∀ v : V, ∀ U : Finset (Lk G v), U.Nonempty → (∃ j, j∉U) →
      3 ≤ ((U ×ˢ (Finset.univ\U)).filter (fun a => G.Adj a.1.val a.2.val)).card)
    (book : ∀ e : Edges G, (∑ t : Triangles G, if e ∈ incidentTriangles G t then (1:ℕ) else 0)=3)
    (v : V) (x : Fin 4 → V) (xi : Function.Injective x)
    (sp : ∀ i, G.Adj v (x i)) (rim : ∀ i, G.Adj (x i) (x (i+1))) :
    ∃ c : V→V→Bool, (∀ a b,c a b=c b a) ∧ BikovLocal.Safe G.Adj c := by
  classical
  let E := edgeRost G
  let Tr := triRost G
  have ec (e : Edges G) : (E e).card=2 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  have tc (t : Triangles G) : (Tr t).card=3 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp t.property).card_eq
  have cl : HostWagnerLinks.TrianglesClosed E Tr := by
    intro t a b ne ha hb
    exact (host_iff_of_ne G ne).mpr
      ((SimpleGraph.mem_cliqueFinset_iff.mp t.property).isClique ha hb ne)
  have xv (i : Fin 4) : x i ≠ v := (sp i).ne.symm
  have hs (i : Fin 4) : hostRel E v (x i) := (host_iff_of_ne G (sp i).ne).mpr (sp i)
  have hr (i : Fin 4) : hostRel E (x i) (x (i+1)) := (host_iff_of_ne G (rim i).ne).mpr (rim i)
  have ht (i : Fin 4) : ∃ t, Tr t={v,x i,x (i+1)} :=
    ⟨triangleNode G (sp i) (rim i) (sp (i+1)),rfl⟩
  obtain ⟨spoke,tr,outside,si,ti,oi,shape,origin⟩ :=
    square_data_of_cycle ec v x xi xv hs hr ht
  have n4 : 4 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective x xi
  have small (S : Finset (Edges G)) (T : Finset (Triangles G))
      (d : Disjoint S (Finset.univ.image spoke)) (s3 : 3 ≤ S.card)
      (co : cutMass (fun l t => l∈incidentTriangles G t) S T ≤ 5) :
      mass (fun l t => l∈incidentTriangles G t) S T < S.card + T.card := by
    have p4 : 4 ≤ (Finset.univ.image spoke).card := by
      rw [Finset.card_image_of_injective _ si,Finset.card_univ,Fintype.card_fin]
    have hh := small_host_cut E Tr ec tc n4 (actual_local_split G cut)
      (actual_avoid_three G conn linkConn) (Finset.univ.image spoke) p4 S T d s3
      (by simpa only [cutMass,mass,incidentTriangles,hostInc_mem] using co)
    simpa only [mass,incidentTriangles,hostInc_mem] using hh
  obtain ⟨c,good⟩ := cubic_coloring_of_ordered_square (incidentTriangles G)
    (hostInc_row E Tr ec tc cl) book spoke tr outside si ti oi shape small
    (actual_coTriangle_connected G conn linkConn (spoke 0) v origin)
  exact to_safe_of_mixed G c good

#print axioms actual_book_three_square_safe
end Erdős151.H13
