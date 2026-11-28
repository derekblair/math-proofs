import N63Sender
import N63HostCensus

namespace Erdos151H13
open Finset NineLinkPivot
open scoped BigOperators
open Erdős151 Erdos151H12

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem fullDeg_near_subtype (S : Finset V) (x : ↥S) :
    Erdos151N63.fullDeg (fun a b : ↥S => G a.val b.val) x = deg G S x.val := by
  let F : Finset ↥S := Finset.univ.filter (fun y : ↥S => G x.val y.val)
  let e : ↥S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have z : F.map e = near G S x.val := by
    ext y
    simp only [F,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,near]
    refine ⟨?_,?_⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,ha⟩
    · rintro ⟨ys,xy⟩
      exact ⟨⟨y,ys⟩,xy,rfl⟩
  change F.card = (near G S x.val).card
  rw [←z,Finset.card_map]

private theorem chart83_constants :
    (∑ i : Fin 9, Erdos151N63.deg Erdos151N63.chart83 9 i.val)=28 ∧
    ∀ i : Fin 9, i.val ∈ Erdos151N63.common83 → Erdos151N63.deg Erdos151N63.chart83 9 i.val=3 := by decide
private theorem chart88_constants :
    (∑ i : Fin 9, Erdos151N63.deg Erdos151N63.chart88 9 i.val)=28 ∧
    ∀ i : Fin 9, i.val ∈ Erdos151N63.common88 → Erdos151N63.deg Erdos151N63.chart88 9 i.val=3 := by decide

theorem exception_relabel {W : Type*} (H : W → W → Prop)
    (rows chart perm : Array Nat) (e : Fin 9 ≃ W)
    (rep : ∀ i j : Fin 9, Erdos151N63.adj rows i.val j.val=true ↔ H (e i) (e j))
    (h : Erdos151N63.relabelOK rows chart 9 (Erdos151N63.mapFin perm)) :
    ∃ e' : Fin 9 ≃ W, ∀ i j : Fin 9, Erdos151N63.adj chart i.val j.val=true ↔ H (e' i) (e' j) := by
  let k : Fin 9 ≃ Fin 9 := Equiv.ofBijective (Erdos151N63.mapFin perm)
    ⟨h.1,Finite.surjective_of_injective h.1⟩
  refine ⟨k.symm.trans e,?_⟩
  intro i j
  have hi : Erdos151N63.mapFin perm (k.symm i) = i := k.apply_symm_apply i
  have hj : Erdos151N63.mapFin perm (k.symm j) = j := k.apply_symm_apply j
  have q := h.2 (k.symm i) (k.symm j)
  rw [hi,hj] at q
  rw [←q]
  exact rep (k.symm i) (k.symm j)

/-- Entire dense-nine sender classification, including initial exhaustive
host chart normalization and exceptional actual routing. -/
theorem sender_of_dense_nine
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : ∀ a b, C a b → G a b) (symC : ∀ {a b}, C a b → C b a)
    (coreNonlone : ∀ a b, C a b → ¬Lone G a b)
    (w : V) (r9 : (neighbors C w).card=9)
    (min2 : ∀ a ∈ neighbors C w, 2 ≤ deg C (neighbors C w) a)
    (density : 28 ≤ ∑ a ∈ neighbors C w, deg C (neighbors C w) a)
    (min8 : ∀ a ∈ neighbors C w, 8 ≤ (neighbors C a).card)
    (max12 : ∀ a, (neighbors G a).card ≤ 12) (size63 : 63 ≤ Fintype.card V)
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    ∃ v, SenderData G C w v := by
  let S := neighbors C w
  let H := fun a b : ↥S => G a.val b.val
  have mono (x : V) : deg C S x ≤ deg G S x := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨ys,xy⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨ys,sub _ _ xy⟩
  have hs (a b : ↥S) : H a b ↔ H b a := ⟨sym,sym⟩
  have ht (a b c : ↥S) (ab : H a b) (ac : H a c) : ¬H b c := by
    have loc (x : ↥S) : G w x.val := sub _ _ ((mem_neighbors C).mp x.property)
    exact fun bc => link w a.val b.val c.val (loc a) (loc b) (loc c) ab bc ac
  have hm (a : ↥S) : 2 ≤ Erdos151N63.fullDeg H a := by
    rw [show Erdos151N63.fullDeg H a = deg G S a.val from fullDeg_near_subtype G S a]
    exact (min2 _ a.property).trans (mono _)
  have sum : 28 ≤ ∑ a : ↥S, Erdos151N63.fullDeg H a := by
    change 28 ≤ ∑ a ∈ S.attach, Erdos151N63.fullDeg H a
    simp only [show ∀ a : ↥S, Erdos151N63.fullDeg H a=deg G S a.val from fullDeg_near_subtype G S]
    rw [Finset.sum_attach]
    exact density.trans (Finset.sum_le_sum (fun a _ => mono a))
  have size : Fintype.card ↥S=9 := by simpa using r9
  obtain ⟨⟨rows,d⟩,e,h,rep⟩ :=
    Erdos151N63.nine_complete_host H size hs (fun a => irr _) ht hm sum
  cases d with
  | pivot x y L =>
      obtain ⟨pc,pr⟩ := h
      exact False.elim (noFree (free13_of_numbered_chart G C w rows e rep sym irr link R41 sub symC
        coreNonlone x y L pc pr (fun a h => min8 a ((mem_neighbors C).mpr h)) max12 size63))
  | exception83 p =>
      obtain ⟨j,adj⟩ := exception_relabel H rows Erdos151N63.chart83 p e rep h
      refine ⟨(j ⟨8,by decide⟩).val,?_⟩
      exact sender_of_exception_chart G C sym irr link R41 sub symC coreNonlone
        w Erdos151N63.chart83 j adj ⟨8,by decide⟩ Erdos151N63.common83 (by decide)
        Erdos151N63.chart83_shape.2.2.2 chart83_constants.2
        (fun i hi k hk diff => ⟨_,Erdos151N63.exception83_centers i hi k hk diff⟩)
        chart83_constants.1 density min8 max12 size63 noFree
  | exception88 p =>
      obtain ⟨j,adj⟩ := exception_relabel H rows Erdos151N63.chart88 p e rep h
      refine ⟨(j ⟨6,by decide⟩).val,?_⟩
      exact sender_of_exception_chart G C sym irr link R41 sub symC coreNonlone
        w Erdos151N63.chart88 j adj ⟨6,by decide⟩ Erdos151N63.common88 (by decide)
        Erdos151N63.chart88_shape.2.2.2 chart88_constants.2
        (fun i hi k hk diff => ⟨_,Erdos151N63.exception88_centers i hi k hk diff⟩)
        chart88_constants.1 density min8 max12 size63 noFree

#print axioms sender_of_dense_nine
end Erdos151H13
