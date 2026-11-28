import MixedComponents
import Mathlib.Data.Finset.Prod

open scoped BigOperators
namespace H13MixedComponents
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open H13PetersenComponents Erdős151.H13 Erdős151.H12 Erdős151.H12.Wagner
open Finset

/-- A checked local model. Different vertices may use different templates. -/
structure Template where
  n : ℕ
  adj : Fin n → Fin n → Bool
  cubic : ∀ i, (univ.filter (fun j => adj i j = true)).card = 3
  delete : ∀ U : Finset (Fin n), U.card ≤ 2 → ∀ a b, a∉U → b∉U →
    Relation.ReflTransGen (fun x y => adj x y = true ∧ x∉U ∧ y∉U) a b
  cut : ∀ U : Finset (Fin n), U.Nonempty → (∃ j,j∉U) →
    3 ≤ ((U ×ˢ (univ \ U)).filter (fun a => adj a.1 a.2 = true)).card
  kind : (∃ x : Fin 4 → Fin n, Function.Injective x ∧ ∀ i, adj (x i) (x (i+1))=true) ∨
    (∃ iso : Fin n ≃ Fin 10, ∀ a b, adj a b=true ↔ PetersenAdj (iso a) (iso b))

def HasTemplate {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ T : Template, ∃ iso : Lk G v ≃ Fin T.n, ∀ a b, G.Adj a.val b.val ↔ T.adj (iso a) (iso b) = true

section Transport
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem template_delete (cert : ∀ v, HasTemplate G v) : LinkDeletionConnected G := by
  classical
  intro v U small a b ha hb
  obtain ⟨T,f,eq⟩ := cert v
  let S := U.map f.toEmbedding
  have hm (x : Lk G v) : f x ∈ S ↔ x ∈ U := by simp [S]
  have p := T.delete S (by simpa [S] using small) (f a) (f b)
    (fun h=>ha ((hm _).mp h)) (fun h=>hb ((hm _).mp h))
  have lift {c d : Fin T.n}
      (h : Relation.ReflTransGen (fun x y => T.adj x y = true ∧ x∉S ∧ y∉S) c d) :
      Relation.ReflTransGen (fun x y : Lk G v => G.Adj x.val y.val ∧ x∉U ∧ y∉U)
        (f.symm c) (f.symm d) := by
    induction h with
    | refl => exact .refl
    | @tail c d _ hd ih =>
      apply ih.tail
      refine ⟨(eq _ _).mpr (by simpa using hd.1),?_,?_⟩
      · intro hx
        exact hd.2.1 (by simpa using (hm (f.symm c)).mpr hx)
      · intro hx
        exact hd.2.2 (by simpa using (hm (f.symm d)).mpr hx)
  simpa using lift p

theorem template_cut (cert : ∀ v, HasTemplate G v) (v : V) (U : Finset (Lk G v))
    (hU : U.Nonempty) (hC : ∃ j,j∉U) :
    3 ≤ ((U ×ˢ (univ \ U)).filter (fun a => G.Adj a.1.val a.2.val)).card := by
  classical
  obtain ⟨T,f,eq⟩ := cert v
  let S := U.map f.toEmbedding
  have hm (x : Lk G v) : f x ∈ S ↔ x ∈ U := by simp [S]
  let A := (U ×ˢ (univ \ U)).filter (fun a => G.Adj a.1.val a.2.val)
  let B := (S ×ˢ (univ \ S)).filter (fun a => T.adj a.1 a.2 = true)
  let fp := (Equiv.prodCongr f f).toEmbedding
  have same : A.map fp = B := by
    ext b
    obtain ⟨a,rfl⟩ := (Equiv.prodCongr f f).surjective b
    change fp a ∈ A.map fp ↔ fp a ∈ B
    constructor
    · intro h
      obtain ⟨c,hc,he⟩ := mem_map.mp h
      have z : c=a := fp.injective he
      subst c
      have hc' : (a.1∈U ∧ a.2∉U) ∧ G.Adj a.1.val a.2.val := by
        simpa [A] using hc
      change (f a.1,f a.2) ∈ B
      simpa [B,hm,eq] using hc'
    · intro h
      refine mem_map.mpr ⟨a,?_,rfl⟩
      change (f a.1,f a.2) ∈ B at h
      simpa [A,B,hm,eq] using h
  have nm : S.Nonempty := by
    obtain ⟨x,hx⟩ := hU
    exact ⟨f x,(hm x).mpr hx⟩
  have ns : ∃ j,j∉S := by
    obtain ⟨x,hx⟩ := hC
    exact ⟨f x,fun h=>hx ((hm x).mp h)⟩
  have h := T.cut S nm ns
  change 3 ≤ B.card at h
  rw [←same,card_map] at h
  exact h

theorem template_kind (cert : ∀ v, HasTemplate G v) (v : V) :
    SquareAt G v ∨ (∃ iso : Lk G v ≃ Fin 10,
      ∀ a b, G.Adj a.val b.val ↔ PetersenAdj (iso a) (iso b)) := by
  obtain ⟨T,f,eq⟩ := cert v
  rcases T.kind with ⟨x,inj,edges⟩|⟨iso,same⟩
  · let y := fun i => f.symm (x i)
    exact Or.inl ⟨fun i => (y i).val,
      fun i j h => inj (f.symm.injective (Subtype.ext h)),
      fun i => (y i).property,fun i => (eq _ _).mpr (by simpa [y] using edges i)⟩
  · exact Or.inr ⟨f.trans iso,fun a b => (eq a b).trans (same (f a) (f b))⟩

theorem template_cubic (cert : ∀ v, HasTemplate G v) (v : V) (a : Lk G v) :
    ((univ : Finset (Lk G v)).filter (fun b=>G.Adj a.val b.val)).card=3 := by
  classical
  obtain ⟨T,f,eq⟩ := cert v
  let U := (univ : Finset (Lk G v)).filter (fun b=>G.Adj a.val b.val)
  have h : U.map f.toEmbedding = univ.filter (fun b => T.adj (f a) b=true) := by
    ext b
    obtain ⟨z,rfl⟩ := f.surjective b
    change f.toEmbedding z ∈ U.map f.toEmbedding ↔ f z ∈ _
    simp [U,eq]
  have hc := congrArg Finset.card h
  rw [card_map,T.cubic] at hc
  exact hc

/-- Three neighbors of each link vertex are precisely the three host
triangles through the corresponding spoke edge. -/
theorem template_book (cert : ∀ v, HasTemplate G v) (e : Edges G) :
    (∑ t : Triangles G, if e ∈ incidentTriangles G t then (1:ℕ) else 0)=3 := by
  classical
  have ec : e.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).card_eq
  obtain ⟨a,b,ab,he⟩ := card_eq_two.mp ec
  have adj : G.Adj a b := (SimpleGraph.mem_cliqueFinset_iff.mp e.property).isClique
    (by simp [he]) (by simp [he]) ab
  let C := {x : Lk G a // G.Adj b x.val}
  let D := {t : Triangles G // e ∈ incidentTriangles G t}
  let F : C → D := fun x => ⟨triangleNode G adj x.property x.val.property,
    (hostInc_mem _ _ _ _).mpr (by
      change e.val ⊆ ({a,b,x.val.val} : Finset V)
      rw [he]
      simp [insert_subset_iff])⟩
  have inj : Function.Injective F := by
    intro x y h
    have e' : ({a,b,x.val.val}:Finset V) = {a,b,y.val.val} :=
      congrArg (fun t : D => t.val.val) h
    have hm : x.val.val ∈ ({a,b,y.val.val}:Finset V) := by rw [←e']; simp
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with ha|hb|hxy
    · exact (x.val.property.ne ha.symm).elim
    · exact (x.property.ne hb.symm).elim
    · exact Subtype.ext (Subtype.ext hxy)
  have surj : Function.Surjective F := by
    intro t
    have incl : e.val ⊆ t.val.val := (hostInc_mem _ _ _ _).mp t.property
    have tc : t.val.val.card=3 := (SimpleGraph.mem_cliqueFinset_iff.mp t.val.property).card_eq
    obtain ⟨x,hxt,hxe⟩ := exists_mem_notMem_of_card_lt_card (show e.val.card<t.val.val.card by omega)
    have ha : a ∈ t.val.val := incl (by simp [he])
    have hb : b ∈ t.val.val := incl (by simp [he])
    have ax : a ≠ x := fun h => hxe (by rw [←h,he]; simp)
    have bx : b ≠ x := fun h => hxe (by rw [←h,he]; simp)
    have ax' := (SimpleGraph.mem_cliqueFinset_iff.mp t.val.property).isClique ha hxt ax
    have bx' := (SimpleGraph.mem_cliqueFinset_iff.mp t.val.property).isClique hb hxt bx
    refine ⟨⟨⟨x,ax'⟩,bx'⟩,Subtype.ext (Subtype.ext ?_)⟩
    change ({a,b,x} : Finset V) = t.val.val
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨ha,insert_subset_iff.mpr ⟨hb,singleton_subset_iff.mpr hxt⟩⟩
    · rw [tc]
      simp [card_insert_of_notMem (by simp [ab,ax] : a ∉ ({b,x}:Finset V)),
        card_insert_of_notMem (by simpa using bx : b ∉ ({x}:Finset V))]
  have hc : Fintype.card C = 3 :=
    (Fintype.card_subtype (fun x : Lk G a => G.Adj b x.val)).trans
      (template_cubic G cert a ⟨b,adj⟩)
  have hd := (Fintype.card_congr (Equiv.ofBijective F ⟨inj,surj⟩)).symm.trans hc
  change Fintype.card {t : Triangles G // e ∈ incidentTriangles G t} = 3 at hd
  rwa [Fintype.card_subtype,card_filter] at hd

end Transport

/-- Whole-host model labels yield the actual component hypotheses automatically.
The finite book roster is derived rather than taken as an extra premise. -/
theorem mixed_nonRamsey_of_templates {V : Type u} [Fintype V] (G : SimpleGraph V)
    (size : Fintype.card V ≤ 63) (hall : HallProjection63.{u})
    (model : ∀ v, (∃ w,G.Adj v w) → HasTemplate G v) : ¬ BikovLocal.Ramsey G.Adj := by
  classical
  apply mixed_nonRamsey G size hall
  intro i hi
  letI := componentFinite G i
  letI : DecidableEq (Fiber G.Adj i) := defaultEq
  let H := componentGraph G i
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hh : ∀ v, HasTemplate H v := by
    intro v
    have hs : ∃ w, G.Adj v.val w := by
      by_contra no
      obtain ⟨a,b,edge⟩ := hi
      have isolated : ∀ w, ¬ G.Adj v.val w := fun w h => no ⟨w,h⟩
      have only {x y : V} (p : Relation.EqvGen G.Adj x y) : x=v.val ↔ y=v.val := by
        induction p with
        | rel x y h =>
          exact ⟨fun e => (isolated y (e ▸ h)).elim,
            fun e => (isolated x (e ▸ h.symm)).elim⟩
        | refl x => rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      have e := (only (Quotient.exact (v.property.trans a.property.symm))).mp rfl
      exact isolated b.val (e ▸ edge)
    obtain ⟨T,iso,valid⟩ := model v.val hs
    let equiv := neighborEquiv G.Adj i v
    exact ⟨T,equiv.trans iso,fun a b => valid (equiv a) (equiv b)⟩
  exact ⟨template_delete H hh,template_cut H hh,template_book H hh,template_kind H hh⟩

#print axioms mixed_nonRamsey_of_templates
end H13MixedComponents
