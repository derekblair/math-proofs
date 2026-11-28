import N63CheckerBridge
import N63ExceptionShape
import N63CrossCharge

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12 Erdos151Ramsey

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem pivot_lift_center {n : ℕ} (w : V) (rows : Array Nat)
    (e : Fin n ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val)
    (i j : Fin n) (L : List ℕ) (ok : Erdos151N63.pivotOK rows n i.val j.val L) :
    ¬G (e i).val (e j).val ∧ (e i).val ≠ (e j).val ∧
    ∃ A : Finset V, A.card=L.length ∧ Independent G A ∧
      ∀ v ∈ A, C w v ∧ v ≠ (e i).val ∧ v ≠ (e j).val ∧ ¬G (e i).val v ∧ ¬G (e j).val v := by
  classical
  obtain ⟨_,_,ij,aj,nd,center,indep⟩ := ok
  let f : Fin n ↪ V := ⟨fun z => (e z).val,Subtype.val_injective.comp e.injective⟩
  let F := Finset.univ.filter (fun z : Fin n => z.val ∈ L)
  let A := F.map f
  have adjnot (u v : Fin n) (h : Erdos151N63.adj rows u.val v.val=false) :
      ¬ G (e u).val (e v).val := by
    intro q
    have t := (rep u v).mpr q
    simp [h] at t
  have inj (u v : Fin n) (h : u.val ≠ v.val) : (e u).val ≠ (e v).val :=
    fun q => h (congrArg Fin.val (f.injective q))
  have e0 : F.map Fin.valEmbedding = L.toFinset := by
    ext z
    simp only [F,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    refine ⟨?_,?_⟩
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hz
      exact ⟨⟨z,(center z hz).1⟩,hz,rfl⟩
  refine ⟨adjnot i j aj,inj i j ij,A,?_,?_,?_⟩
  · unfold A
    rw [Finset.card_map,←Finset.card_map Fin.valEmbedding,e0,List.toFinset_card_of_nodup nd]
  · intro u hu v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hv
    exact adjnot _ _ (indep _ (Finset.mem_filter.mp hz).2 _ (Finset.mem_filter.mp hq).2)
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    have m : u.val ∈ L := (Finset.mem_filter.mp hu).2
    obtain ⟨_,nx,ny,ax,ay⟩ := center _ m
    exact ⟨(mem_neighbors C).mp (e u).property,inj u i nx,inj u j ny,adjnot i u ax,adjnot j u ay⟩

theorem link_degree_sum_of_chart {n : ℕ} (w : V) (rows : Array Nat)
    (e : Fin n ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val) :
    (∑ x ∈ neighbors C w, actualLinkDegree G C w x) = ∑ i : Fin n, Erdos151N63.deg rows n i.val := by
  rw [←Finset.sum_attach]
  change (∑ x : ↥(neighbors C w), actualLinkDegree G C w x.val) = _
  symm
  exact Fintype.sum_equiv e _ _ (fun i => (actual_degree_of_chart G C w rows e rep i).symm)

/-- Density equality upgrades the ambient chart to the actual core chart. -/
theorem core_chart_of_ambient_density {n : ℕ} (w : V) (rows : Array Nat)
    (e : Fin n ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val)
    (sub : ∀ a b, C a b → G a b)
    (d : (∑ i : Fin n, Erdos151N63.deg rows n i.val) ≤ ∑ x ∈ neighbors C w, deg C (neighbors C w) x) :
    (∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ C (e i).val (e j).val) ∧
    (∑ x ∈ neighbors C w, deg C (neighbors C w) x) = ∑ i : Fin n, Erdos151N63.deg rows n i.val := by
  let S := neighbors C w
  have inc (x : V) : near C S x ⊆ neighbors G x ∩ S := by
    intro y h
    obtain ⟨hy,hc⟩ := mem_filter.mp h
    exact mem_inter.mpr ⟨(mem_neighbors G).mpr (sub _ _ hc),hy⟩
  have le (x : V) (hx : x∈S) : deg C S x ≤ actualLinkDegree G C w x := card_le_card (inc x)
  have eq := link_degree_sum_of_chart G C w rows e rep
  change (∑ x ∈ S, actualLinkDegree G C w x) = _ at eq
  have cmp := Finset.sum_le_sum le
  change _ ≤ ∑ x ∈ S, deg C S x at d
  have total : (∑ x ∈ S, deg C S x) = ∑ x ∈ S, actualLinkDegree G C w x := by omega
  have each := (Finset.sum_eq_sum_iff_of_le le).mp total
  refine ⟨?_,total.trans eq⟩
  intro i j
  rw [rep]
  constructor
  · intro g
    have nEq : near C S (e i).val = neighbors G (e i).val∩S :=
      Finset.eq_of_subset_of_card_le (inc _) (each _ (e i).property).ge
    have r : (e j).val ∈ neighbors G (e i).val∩S :=
      mem_inter.mpr ⟨(mem_neighbors G).mpr g,(e j).property⟩
    rw [←nEq] at r
    exact (mem_filter.mp r).2
  · exact sub _ _

#print axioms pivot_lift_center
#print axioms core_chart_of_ambient_density
end Erdos151H13
