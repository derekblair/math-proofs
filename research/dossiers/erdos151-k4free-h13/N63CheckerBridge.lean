import N63ActualLink
import N63ChartChecker

namespace Erdos151H13
open Erdős151 Erdos151H12 Erdos151Ramsey
open scoped Classical

private theorem chart_outer_eq (a b s : ℕ) :
    Erdos151N63.outerFloor a b s = outerFloor a b s := by
  unfold Erdos151N63.outerFloor outerFloor alphaFloorFour Erdos151N63.alphaFloor alphaFloor
  have ha : ¬ 9 ≤ 7-a-s := by omega
  have hb : ¬ 9 ≤ 7-b-s := by omega
  simp [ha,hb]

private theorem card_of_fin_lift {n : ℕ} (S : List ℕ)
    (nd : S.Nodup) (bounds : ∀ i ∈ S, i<n) :
    (Finset.univ.filter (fun i : Fin n => i.val ∈ S)).card = S.length := by
  classical
  let F := Finset.univ.filter (fun i : Fin n => i.val ∈ S)
  have eq : F.map Fin.valEmbedding = S.toFinset := by
    ext i
    simp only [F, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    refine ⟨?_,?_⟩
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro hi
      exact ⟨⟨i,bounds i hi⟩,hi,rfl⟩
  rw [← Finset.card_map Fin.valEmbedding,eq,List.toFinset_card_of_nodup nd]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem actual_degree_of_chart {n : ℕ} (w : V) (rows : Array Nat)
    (e : Fin n ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val)
    (i : Fin n) :
    actualLinkDegree G C w (e i).val = Erdos151N63.deg rows n i.val := by
  classical
  let p (j : ℕ) := Erdos151N63.adj rows i.val j
  let S := (List.range n).filter p
  let F := Finset.univ.filter (fun j : Fin n => j.val ∈ S)
  let emb : Fin n ↪ V := ⟨fun j => (e j).val,Subtype.val_injective.comp e.injective⟩
  have eq : F.map emb = neighbors G (e i).val∩neighbors C w := by
    ext z
    constructor
    · intro hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
      have hj' := (Finset.mem_filter.mp hj).2
      change j.val ∈ S at hj'
      have hp := (List.mem_filter.mp hj').2
      exact Finset.mem_inter.mpr ⟨(mem_neighbors G).mpr ((rep i j).mp hp),(e j).property⟩
    · intro hz
      obtain ⟨hz',hw⟩ := Finset.mem_inter.mp hz
      let j := e.symm ⟨z,hw⟩
      have jj : e j = ⟨z,hw⟩ := e.apply_symm_apply _
      refine Finset.mem_map.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,?_⟩,congrArg Subtype.val jj⟩
      change j.val ∈ S
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr j.isLt,(rep i j).mpr ?_⟩
      simpa only [jj] using (mem_neighbors G).mp hz'
  have c := card_of_fin_lift S ((List.nodup_range).filter p)
    (fun j hj => List.mem_range.mp (List.mem_filter.mp hj).1)
  unfold actualLinkDegree Erdos151N63.deg
  rw [←eq,Finset.card_map]
  exact c

/-- Turn a checked adjacency/price row and its independent center list into
an actual free13 set in the ambient graph, with only the published R41 input. -/
theorem free13_of_numbered_chart {n : ℕ} (w : V) (rows : Array Nat)
    (e : Fin n ≃ ↥(neighbors C w))
    (rep : ∀ i j : Fin n, Erdos151N63.adj rows i.val j.val = true ↔ G (e i).val (e j).val)
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬ G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ m, 41 ≤ m → Erdős151.H10.TriangleIndependentTen (Fin m))
    (sub : ∀ a b, C a b → G a b) (Csym : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬ Lone G a b)
    (x y : ℕ) (S : List ℕ) (ok : Erdos151N63.pivotOK rows n x y S)
    (price : Erdos151N63.priceOK n (Erdos151N63.deg rows n x) (Erdos151N63.deg rows n y) S.length)
    (minC : ∀ v, C w v → 8 ≤ (neighbors C v).card)
    (maxG : ∀ v, (neighbors G v).card ≤ 12) (ord : 63 ≤ Fintype.card V) :
    ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V) := by
  classical
  obtain ⟨hx,hy,hxy,adjxy,nd,center,indep⟩ := ok
  let i : Fin n := ⟨x,hx⟩
  let j : Fin n := ⟨y,hy⟩
  let f : Fin n ↪ V := ⟨fun z => (e z).val,Subtype.val_injective.comp e.injective⟩
  let F := Finset.univ.filter (fun z : Fin n => z.val ∈ S)
  let A := F.map f
  have cwx := (mem_neighbors C).mp (e i).property
  have cwy := (mem_neighbors C).mp (e j).property
  have adjnot (u v : Fin n) (h : Erdos151N63.adj rows u.val v.val=false) :
      ¬ G (e u).val (e v).val := by
    intro a
    have p := (rep u v).mpr a
    simp [h] at p
  have inj (u v : Fin n) (h : u.val ≠ v.val) : (e u).val ≠ (e v).val :=
    fun q => h (congrArg Fin.val (f.injective q))
  have pA : ∀ v ∈ A, C w v ∧ v ≠ (e i).val ∧ v ≠ (e j).val ∧
      ¬ G (e i).val v ∧ ¬ G (e j).val v := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    have m : u.val ∈ S := (Finset.mem_filter.mp hu).2
    obtain ⟨_,nx,ny,ax,ay⟩ := center _ m
    exact ⟨(mem_neighbors C).mp (e u).property,inj u i nx,inj u j ny,adjnot i u ax,adjnot j u ay⟩
  have iA : Independent G A := by
    intro u hu v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hv
    exact adjnot _ _ (indep _ (Finset.mem_filter.mp hz).2 _ (Finset.mem_filter.mp hq).2)
  have len : A.card=S.length := by
    rw [Finset.card_map]
    exact card_of_fin_lift S nd (fun z hz => (center z hz).1)
  have size : (neighbors C w).card=n := by
    simpa using (Fintype.card_congr e).symm
  apply free13_of_local_chart G C sym irr link R41 sub Csym coreNonlone (e i).val w (e j).val
    cwx cwy (adjnot i j adjxy) (inj i j hxy) (minC _ cwx) (minC _ cwy) A pA iA ord
    (D:=36) (by have :=maxG (e i).val; have :=maxG (e j).val; have := maxG w; omega) (maxG _)
  intro a b s al au bl bu hs
  rw [actual_degree_of_chart G C w rows e rep i] at al au
  rw [actual_degree_of_chart G C w rows e rep j] at bl bu
  rw [size] at au bu
  change Erdos151N63.deg rows n x ≤ a at al
  change a ≤ Erdos151N63.deg rows n x + ((neighbors G w).card - n) at au
  change Erdos151N63.deg rows n y ≤ b at bl
  change b ≤ Erdos151N63.deg rows n y + ((neighbors G w).card - n) at bu
  have hi : a ≤ Erdos151N63.deg rows n x + (12-n) := by have := maxG w; exact au.trans (by omega)
  have hj : b ≤ Erdos151N63.deg rows n y + (12-n) := by have := maxG w; exact bu.trans (by omega)
  have n12 : n ≤ 12 := by
    have c := Finset.card_le_card (s:=neighbors C w) (t:=neighbors G w)
      (fun z hz => (mem_neighbors G).mpr (sub w z ((mem_neighbors C).mp hz)))
    have := maxG w
    omega
  have q := Erdos151N63.price_transfer n _ _ _ a b s price al bl hi hj hs n12
  rw [chart_outer_eq] at q
  omega

#print axioms actual_degree_of_chart
#print axioms free13_of_numbered_chart
end Erdos151H13
