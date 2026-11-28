import H12ExactBook
import WagnerFin8

namespace Erdos151H12
open Erdos151CoreHigh Erdos151MarkedLinkTable

def row6Order (i : Fin 8) : Fin 8 := ⟨(3*i.val)%8, Nat.mod_lt _ (by decide)⟩

def row6Permutation : Fin 8 ≃ Fin 8 :=
  ⟨row6Order,row6Order,by decide +kernel,by decide +kernel⟩

theorem row6_adj_permutation :
    ∀ i j : Fin 8, WagnerFin8.Adj i j ↔ adj 6 (row6Permutation i) (row6Permutation j)=true := by
  decide +kernel

theorem row12_degree_three_forces6 :
    ∀ k : Fin 7, (edges k).length=12 → (∀ i : Fin 8, deg k i=3) → k=6 := by
  decide

variable {V : Type*} [DecidableEq V] [Fintype V] (C : V → V → Prop) [DecidableRel C]

/-- Under the no-surplus density endpoint, every active vertex has an
actual Wagner adjacency relabeling onto its neighbor subtype. -/
theorem wagner_iso_after_density
    (sym : ∀ {a b}, C a b → C b a) (irr : ∀ a, ¬C a a)
    (atlas12 : ∀ u, (neighbors C u).Nonempty →
       ∃ L : NamedLink (neighbors C) (ambientCodeg C) u, (edges L.kind).length=12) :
    ∀ w, (neighbors C w).Nonempty →
      ∃ E : Fin 8 ≃ {x : V // x≠w ∧ C w x},
        ∀ i j : Fin 8, WagnerFin8.Adj i j ↔ C (E i).val (E j).val := by
  intro w hw
  obtain ⟨L,hL⟩ := atlas12 w hw
  have exactBook := exact_book_after_density C sym irr atlas12
  have localBook (i : Fin 8) : C w (L.emb i) :=
    (mem_neighbors C).mp (NamedLink.mem _ _ w L i)
  have hKind : L.kind=6 :=
    row12_degree_three_forces6 _ hL (fun i => (L.book i).symm.trans (exactBook w _ (localBook i)))
  let f (i : Fin 8) : {x : V // x≠w ∧ C w x} :=
    ⟨L.emb i,fun eq => irr w (by simpa only [eq] using localBook i),localBook i⟩
  have bij : Function.Bijective f := by
    constructor
    · exact fun u v e => L.emb.injective (congrArg Subtype.val e)
    · intro x
      obtain ⟨i,hi⟩ := NamedLink.get _ _ w L ((mem_neighbors C).mpr x.property.2)
      exact ⟨i,Subtype.ext hi⟩
  let E := row6Permutation.trans (Equiv.ofBijective f bij)
  refine ⟨E,?_⟩
  intro i j
  change WagnerFin8.Adj i j ↔ C (L.emb (row6Permutation i)) (L.emb (row6Permutation j))
  rw [row6_adj_permutation,←hKind,←L.induced]
  exact mem_neighbors C

#print axioms wagner_iso_after_density
end Erdos151H12
