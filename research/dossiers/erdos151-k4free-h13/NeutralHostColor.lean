import MixedCatalog
import WagnerFin8
import MixedAtlasEight
import H12WagnerAdapter

open scoped BigOperators
namespace H13MixedComponents
open Finset H13PetersenComponents Erdos151H12 Erdős151.H13 Erdős151.Upper
  Erdos151CoreHigh Erdos151MarkedLinkTable
variable {V : Type u} [Fintype V] [DecidableEq V]

def graphOf (C : V → V → Prop) (sym : BikovLocal.Sym C)
    (irr : BikovLocal.Loopless C) : SimpleGraph V where
  Adj := C
  symm := ⟨fun _ _ h => sym h⟩
  loopless := ⟨irr⟩

def hostWSquare (i : Fin 4) : Fin 8 :=
  (#[(0:Fin 8),1,5,4] : Array (Fin 8))[i.val]!

private theorem hostWSquare_inj : Function.Injective hostWSquare := by decide +kernel
private theorem hostWSquare_adj : ∀ i, WagnerFin8.Adj (hostWSquare i) (hostWSquare (i+1)) := by decide +kernel

def hostWTemplate : Template where
  n := 8
  adj := fun a b => decide (WagnerFin8.Adj a b)
  cubic := by
    intro a
    simpa using WagnerFin8.degree a
  delete := by
    intro U card a b ha hb
    simpa using WagnerFin8.connected_after_two U card a b ha hb
  cut := by
    intro U hU co
    have small : U.card<8 := by
      obtain ⟨x,hx⟩ := co
      have h := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_univ U,fun eq=>hx (eq.symm ▸ mem_univ x)⟩)
      simpa using h
    simpa using WagnerFin8.edge_cut U (card_pos.mpr hU) small
  kind := Or.inl ⟨hostWSquare,hostWSquare_inj,by simpa using hostWSquare_adj⟩


theorem actual_wagner_template (C : V → V → Prop) [DecidableRel C]
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C) (v : V)
    (L : NamedLink (neighbors C) (ambientCodeg C) v) (hk : L.kind=6) :
    HasTemplate (graphOf C sym irr) v := by
  let φ : Fin 8 → Lk (graphOf C sym irr) v := fun i =>
    ⟨L.emb i,(mem_neighbors C).mp (NamedLink.mem _ _ v L i)⟩
  have bij : Function.Bijective φ :=
    ⟨fun a b h => L.emb.injective (congrArg Subtype.val h),fun x => by
      obtain ⟨j,h⟩ := NamedLink.get _ _ v L ((mem_neighbors C).mpr x.property)
      exact ⟨j,Subtype.ext h⟩⟩
  let p := row6Permutation.trans (Equiv.ofBijective φ bij)
  refine ⟨hostWTemplate,p.symm,?_⟩
  intro a b
  change C a.val b.val ↔ decide (WagnerFin8.Adj (p.symm a) (p.symm b)) = true

  obtain ⟨i,rfl⟩ := p.surjective a
  obtain ⟨j,rfl⟩ := p.surjective b
  simp only [Equiv.symm_apply_apply]
  change C (L.emb (row6Permutation i)) (L.emb (row6Permutation j)) ↔
    decide (WagnerFin8.Adj i j) = true
  rw [decide_eq_true_eq,row6_adj_permutation,←hk,←L.induced]
  exact (mem_neighbors C).symm

/-- Final neutral endpoint from the actual n63 tight-core output. The
remaining graph input is the literal exact ten-chart atlas equivalence,
not an assumption of a globally uniform link type. -/
theorem nonRamsey_of_neutral_shapes (C : V → V → Prop) [DecidableRel C]
    (sym : BikovLocal.Sym C) (irr : BikovLocal.Loopless C)
    (size : Fintype.card V ≤ 63) (hall : HallProjection63.{u})
    (shapes : ∀ v, (neighbors C v).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) v, (edges L.kind).length=12) ∨
      ((neighbors C v).card=10 ∧ ∀ a∈neighbors C v,
        NineLinkPivot.deg C (neighbors C v) a=3))
    (ten : ∀ w, (neighbors C w).card=10 →
      (∀ a∈neighbors C w, NineLinkPivot.deg C (neighbors C w) a=3) → HasTemplate (graphOf C sym irr) w) :
    ¬ BikovLocal.Ramsey C := by
  have shaped : ∀ u, (neighbors C u).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) u, (edges L.kind).length=12) ∨
      (∀ v∈neighbors C u, ambientCodeg C u v=3) := by
    intro w hw
    rcases shapes w hw with h|⟨_,h⟩
    · exact Or.inl h
    · right
      intro v hv
      rw [← row_core_codeg C]
      exact h v hv
  have wagner := neutral_eight_is_wagner C (fun {_ _} h => sym h) irr shaped
  apply mixed_nonRamsey_of_templates (graphOf C sym irr) size hall
  intro v hv
  obtain ⟨x,hx⟩ := hv
  rcases shapes v ⟨x,(mem_neighbors C).mpr hx⟩ with ⟨L,hL⟩|⟨r,h⟩
  · exact actual_wagner_template C sym irr v L (wagner v L hL)
  · exact ten v r h

#print axioms nonRamsey_of_neutral_shapes
end H13MixedComponents
