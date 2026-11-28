import CoreDensityColor

namespace Erdős151.H12
open Wagner

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem pair_label (c : V→V→Bool) (cs : ∀ a b,c a b=c b a)
    {u v a b : V} (uv : u≠v) (he : ({u,v}:Finset V)={a,b}) : c u v=c a b := by
  have hu : u∈({a,b}:Finset V) := by rw [←he]; simp
  have hv : v∈({a,b}:Finset V) := by rw [←he]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> first
    | exact False.elim (uv rfl)
    | rfl
    | exact cs _ _

private theorem edge_pair_repr (G : SimpleGraph V) [DecidableRel G.Adj] (e : Edges G) :
    ∃ a b : V, G.Adj a b ∧ e.val={a,b} := by
  have h := SimpleGraph.mem_cliqueFinset_iff.mp e.property
  obtain ⟨a,b,ne,he⟩ := Finset.card_eq_two.mp h.card_eq
  have ha : a ∈ (e.val:Set V) := by rw [he]; simp
  have hb : b ∈ (e.val:Set V) := by rw [he]; simp
  exact ⟨a,b,h.isClique ha hb ne,he⟩

noncomputable def toTriLabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→V→Bool) (e : Edges G) : Bool :=
  let h := edge_pair_repr G e
  c (Classical.choose h) (Classical.choose (Classical.choose_spec h))

theorem toTriLabel_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→V→Bool) (cs : ∀ a b,c a b=c b a) {a b : V} (ab : G.Adj a b) :
    toTriLabel G c (pairEdge G ab)=c a b := by
  unfold toTriLabel
  let h := edge_pair_repr G (pairEdge G ab)
  have sp := Classical.choose_spec (Classical.choose_spec h)
  exact pair_label c cs sp.1.ne sp.2.symm

private theorem three_bools (x y z : Bool)
    (h : ¬ (x=y ∧ y=z)) :
    (x=true ∨ y=true ∨ z=true) ∧ (x=false ∨ y=false ∨ z=false) := by
  cases x <;> cases y <;> cases z <;> simp_all

private theorem paired_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Triangles G) {a b : V} (ab : G.Adj a b)
    (ha : a∈t.val) (hb : b∈t.val) : pairEdge G ab ∈ TriEdges G t := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro v hv
  change v∈({a,b}:Finset V) at hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl
  · exact ha
  · exact hb

theorem mixed_of_three_safe (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V→V→Bool) (cs : ∀ a b,c a b=c b a)
    (t : Triangles G) (a b d : V) (he : t.val={a,b,d})
    (ab : G.Adj a b) (bd : G.Adj b d) (ad : G.Adj a d)
    (safe : ¬ (c a b=c b d ∧ c b d=c a d)) :
    Mixed (toTriLabel G c) (TriEdges G t) := by
  have ha : a∈t.val := by rw [he]; simp
  have hb : b∈t.val := by rw [he]; simp
  have hd : d∈t.val := by rw [he]; simp
  obtain ⟨p,q⟩ := three_bools (c a b) (c b d) (c a d) safe
  constructor <;> first
    | rcases p with h|h|h
      · exact ⟨pairEdge G ab,paired_mem G t ab ha hb,(toTriLabel_pair G c cs ab).trans h⟩
      · exact ⟨pairEdge G bd,paired_mem G t bd hb hd,(toTriLabel_pair G c cs bd).trans h⟩
      · exact ⟨pairEdge G ad,paired_mem G t ad ha hd,(toTriLabel_pair G c cs ad).trans h⟩
    | rcases q with h|h|h
      · exact ⟨pairEdge G ab,paired_mem G t ab ha hb,(toTriLabel_pair G c cs ab).trans h⟩
      · exact ⟨pairEdge G bd,paired_mem G t bd hb hd,(toTriLabel_pair G c cs bd).trans h⟩
      · exact ⟨pairEdge G ad,paired_mem G t ad ha hd,(toTriLabel_pair G c cs ad).trans h⟩

/-- Edge-minimal Ramsey graphs have at least as many triangles as
edges. Vertices of the legal hypergraph are actual unordered edges. -/
theorem minimal_ramsey_triangle_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (ramsey : BikovLocal.Ramsey G.Adj)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H G.Adj → BikovLocal.Sym H →
      ∀ a b, G.Adj a b → ¬H a b → ¬BikovLocal.Ramsey H) :
    (G.cliqueFinset 2).card ≤ (G.cliqueFinset 3).card := by
  classical
  have nb : ¬ ∃ c : Edges G → Bool, ∀ t : Triangles G, Mixed c (TriEdges G t) := by
    rintro ⟨c,h⟩
    obtain ⟨cc,cs,ok⟩ := to_safe_of_mixed G c h
    exact ramsey cc cs ok
  have full (A : Finset (Triangles G))
      (h : ¬ ∃ c : Edges G → Bool, ∀ t∈A, Mixed c (TriEdges G t)) :
      ∀ e : Edges G, ∃ t∈A, e∈TriEdges G t := by
    intro e
    by_contra! unused
    obtain ⟨u,v,uv,he⟩ := edge_pair_repr G e
    let H := BikovLocal.Removed G.Adj u v
    have sub : BikovLocal.Sub H G.Adj := fun {_ _} x => x.1
    have sym : BikovLocal.Sym H := by
      intro a b h
      refine ⟨h.1.symm,?_⟩
      rintro (⟨p,q⟩|⟨p,q⟩)
      · exact h.2 (Or.inr ⟨q,p⟩)
      · exact h.2 (Or.inl ⟨q,p⟩)
    have no : ¬ BikovLocal.Ramsey H :=
      minimal H sub sym u v uv (fun x => x.2 (Or.inl ⟨rfl,rfl⟩))
    unfold BikovLocal.Ramsey at no
    push Not at no
    obtain ⟨c,cs,ok⟩ := no
    apply h
    refine ⟨toTriLabel G c,fun t ht => ?_⟩
    obtain ⟨a,b,d,ab,ad,bd,hts⟩ :=
      SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp t.property)
    have ay : a∈t.val := by rw [hts]; simp
    have byy : b∈t.val := by rw [hts]; simp
    have dy : d∈t.val := by rw [hts]; simp
    have stays (x y : V) (xy : G.Adj x y) (xx : x∈t.val) (yy : y∈t.val) : H x y := by
      refine ⟨xy, ?_⟩
      intro hc
      have eq : (pairEdge G xy).val=e.val := by
        rw [he]
        change ({x,y}:Finset V)={u,v}
        rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rfl
        · exact Finset.pair_comm _ _
      have em := paired_mem G t xy xx yy
      have ef : pairEdge G xy=e := Subtype.ext eq
      exact unused t ht (ef ▸ em)
    apply mixed_of_three_safe G c cs t a b d hts ab bd ad
    intro hh
    exact ok a b d (stays a b ab ay byy) (stays b d bd byy dy)
      (stays d a ad.symm dy ay) ⟨hh.1,hh.2.trans (cs a d)⟩
  have card := density_of_full_support_obstructions (TriEdges G) nb full
  simpa only [Fintype.card_coe] using card

#print axioms toTriLabel_pair
#print axioms minimal_ramsey_triangle_density
end Erdős151.H12
