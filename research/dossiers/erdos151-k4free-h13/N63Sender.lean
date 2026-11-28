import N63SenderLift

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12 Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

structure SenderData (w v : V) : Prop where
  edge : C w v
  coreNine : (neighbors C w).card = 9
  ambientTwelve : (neighbors G w).card = 12
  score28 : (∑ a ∈ neighbors C w, deg C (neighbors C w) a) = 28
  four : (crossK C w v).card = 4
  price : ∀ x ∈ crossK C w v,
    (neighbors G x∩neighbors G w).card = actualLinkDegree G C w x
  shared : ∀ x ∈ crossK C w v, ∀ y ∈ crossK C w v, x≠y →
    ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card = 0

/-- Connect the two exceptional checked patterns to actual routing data.
An ambient picture alone is not used as a core picture: adjacency equality
is first proved from the core degree-sum hypothesis. -/
theorem sender_of_exception_chart
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b)
    (w : V) (rows : Array Nat) (e : Fin 9 ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin 9, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val)
    (high : Fin 9) (K : List ℕ)
    (highDeg : Erdos151N63.deg rows 9 high.val=4)
    (his : ∀ i : Fin 9, Erdos151N63.adj rows high.val i.val=true ↔ i.val∈K)
    (ks : ∀ i : Fin 9, i.val∈K → Erdos151N63.deg rows 9 i.val=3)
    (centers : ∀ i∈K, ∀ j∈K, i≠j →
      ∃ L : List ℕ, Erdos151N63.pivotOK rows 9 i j L ∧ L.length=2)
    (total28 : (∑ i : Fin 9, Erdos151N63.deg rows 9 i.val)=28)
    (density : 28 ≤ ∑ a ∈ neighbors C w, deg C (neighbors C w) a)
    (min8 : ∀ a ∈ neighbors C w, 8 ≤ (neighbors C a).card)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V)
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    SenderData G C w (e high).val := by
  let v := (e high).val
  have r9 : (neighbors C w).card=9 := by simpa using (Fintype.card_congr e).symm
  obtain ⟨repC,sumC⟩ := core_chart_of_ambient_density G C w rows e rep sub (by rwa [total28])
  have EDGE : C w v := (mem_neighbors C).mp (e high).property
  have four : (crossK C w v).card=4 := by
    unfold crossK
    rw [Finset.inter_comm]
    exact (actual_degree_of_chart C C w rows e repC high).trans highDeg
  have Ck : ∀ i : Fin 9, (e i).val ∈ crossK C w v ↔ i.val∈K := by
    intro i
    have h1 : (e i).val ∈ crossK C w v ↔ C v (e i).val := by
      constructor
      · intro h
        exact (mem_neighbors C).mp (mem_inter.mp h).2
      · intro h
        exact mem_inter.mpr ⟨(e i).property,(mem_neighbors C).mpr h⟩
    exact h1.trans ((repC high i).symm.trans (his i))
  have pair (x : V) (hx : x ∈ crossK C w v) (y : V) (hy : y ∈ crossK C w v)
      (xy : x≠y) :
      (neighbors G x∩neighbors G w).card=3 ∧
      (neighbors G y∩neighbors G w).card=3 ∧
      ((neighbors G x∩neighbors G y)\insert w (neighbors G w)).card=0 ∧
      (neighbors G w).card=12 := by
    let i := e.symm ⟨x,(mem_inter.mp hx).1⟩
    let j := e.symm ⟨y,(mem_inter.mp hy).1⟩
    have ix : (e i).val=x := congrArg Subtype.val (e.apply_symm_apply _)
    have jy : (e j).val=y := congrArg Subtype.val (e.apply_symm_apply _)
    have ik : i.val∈K := (Ck i).mp (ix.symm ▸ hx)
    have jk : j.val∈K := (Ck j).mp (jy.symm ▸ hy)
    have ij : i.val≠j.val := by
      intro h
      have h' := congrArg (fun k : Fin 9 => (e k).val) (Fin.ext h)
      exact xy (ix.symm.trans (h'.trans jy))
    obtain ⟨L,pc,lc⟩ := centers _ ik _ jk ij
    obtain ⟨nG,ne,A,ac,ia,memA⟩ := pivot_lift_center G C w rows e rep i j L pc
    have pd : actualLinkDegree G C w (e i).val=3 :=
      (actual_degree_of_chart G C w rows e rep i).trans (ks i ik)
    have qd : actualLinkDegree G C w (e j).val=3 :=
      (actual_degree_of_chart G C w rows e rep j).trans (ks j jk)
    have h := failed_medium_pair_unique_prices G C sym irr link R41 sub symC coreNonlone
      (e i).val w (e j).val ((mem_neighbors C).mp (e i).property) ((mem_neighbors C).mp (e j).property)
      nG ne (min8 _ (e i).property) (min8 _ (e j).property) r9 size63 (max12 _) (max12 _) (max12 _)
      pd qd A memA ia (by omega) noFree
    rw [ix,jy] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2.2⟩
  obtain ⟨a,ha,b,hb,ab⟩ := pick_two (crossK C w v) (by omega)
  refine ⟨EDGE,r9,(pair a ha b hb ab).2.2.2,sumC.trans total28,four,?_,?_⟩
  · intro x hx
    have ec : 0 < ((crossK C w v).erase x).card := by
      have ec : ((crossK C w v).erase x).card+1 = (crossK C w v).card :=
        Finset.card_erase_add_one hx
      omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp ec
    obtain ⟨ne,yin⟩ := Finset.mem_erase.mp hy
    have a3 := (pair x hx y yin ne.symm).1
    let i := e.symm ⟨x,(mem_inter.mp hx).1⟩
    have ix : (e i).val=x := congrArg Subtype.val (e.apply_symm_apply _)
    have ik : i.val∈K := (Ck i).mp (ix.symm ▸ hx)
    have p := (actual_degree_of_chart G C w rows e rep i).trans (ks i ik)
    rw [ix] at p
    exact a3.trans p.symm
  · exact fun x hx y hy xy => (pair x hx y hy xy).2.2.1

#print axioms sender_of_exception_chart
end Erdos151H13
