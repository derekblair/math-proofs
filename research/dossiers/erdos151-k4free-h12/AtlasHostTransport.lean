import H12Assembler

namespace Erdős151.H12
open Erdos151H12 Erdos151CoreHigh Erdos151MarkedLinkTable

/-- The finite atlas certificate interface, separate from its host lift. -/
def FinEightCertificate : Prop :=
  ∀ (D : Fin 8→Fin 8→Prop),
    (∀ a b,D a b→D b a) → (∀ a,¬D a a) →
    (∀ a b c,D a b→D a c→D b c→False) →
    ∀ c : Fin 8→Fin 8→Bool, (∀ a b,c a b=c b a) →
      (¬∃ f : Fin 8→Bool, ∀ a b,D a b→¬(f a=c a b ∧ f b=c a b)) →
      ∃ i : Fin 7, ∃ σ : Equiv.Perm (Fin 8), ∀ a b,D (σ a) (σ b) ↔ adj i a b=true

theorem atlas_row_degree : ∀ k : Fin 7, ∀ i : Fin 8,
    (Finset.univ.filter (fun j => adj k i j = true)).card=deg k i := by decide +kernel

theorem atlas_host_transport {V : Type*} [Fintype V] [DecidableEq V]
    (cert : FinEightCertificate) : DegreeEightAtlas V := by
  classical
  intro C inst sym irr tri cr minimal w hw
  let S := neighbors C w
  change S.card=8 at hw
  have hcard : Fintype.card ↥S=8 := by simpa only [Fintype.card_coe] using hw
  let slot : Fin 8 ≃ ↥S := (Fintype.equivFinOfCardEq hcard).symm
  have ns (i : Fin 8) : C w (slot i).val := (mem_neighbors C).mp (slot i).property
  let B : V→V→Prop := fun a b=>a≠w ∧ b≠w ∧ C a b
  have Bsub : BikovLocal.Sub B C := fun {_ _} h=>h.2.2
  have Bsym : BikovLocal.Sym B := fun {_ _} h=>⟨h.2.1,h.1,sym h.2.2⟩
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have Cwv : C w v := (mem_neighbors C).mp hv
  obtain ⟨old,cs,ok⟩ := not_ramsey_colors B
    (minimal B Bsub Bsym w v Cwv (fun h=>h.1 rfl))
  let D (a b : Fin 8) := C (slot a).val (slot b).val
  let c (a b : Fin 8) := old (slot a).val (slot b).val
  have blocked : ¬∃ f : Fin 8→Bool, ∀ a b,D a b→¬(f a=c a b ∧ f b=c a b) := by
    intro h
    obtain ⟨f,okf⟩ := h
    let g (x : V) := if hx : x∈S then f (slot.symm ⟨x,hx⟩) else false
    have linked (a b : V) (wa : C w a) (wb : C w b) (ab : C a b) :
        ¬ (g a=old a b ∧ g b=old a b) := by
      have am : a∈S := (mem_neighbors C).mpr wa
      have bm : b∈S := (mem_neighbors C).mpr wb
      let x := slot.symm ⟨a,am⟩
      let y := slot.symm ⟨b,bm⟩
      have hx : (slot x).val=a := congrArg Subtype.val (slot.apply_symm_apply ⟨a,am⟩)
      have hy : (slot y).val=b := congrArg Subtype.val (slot.apply_symm_apply ⟨b,bm⟩)
      have ga : g a=f x := by simp [g,am,x]
      have gb : g b=f y := by simp [g,bm,y]
      rw [ga,gb,←hx,←hy]
      exact okf x y (by change C (slot x).val (slot y).val; rwa [hx,hy])
    obtain ⟨cc,css,good,_⟩ := BikovLocal.lift_link C (fun {_ _} h=>sym h) irr w old cs ok g linked
    exact cr cc css good
  obtain ⟨k,perm,facts⟩ := cert D (fun _ _ h=>sym h) (fun a=>irr (slot a).val)
    (fun a b d ab ad bd=>tri w _ _ _ (ns a) (ns b) (ns d) ab ad bd) c
    (fun a b=>cs _ _) blocked
  let emb : Fin 8 ↪ V := perm.toEmbedding.trans (slot.toEmbedding.trans
    (⟨Subtype.val,Subtype.val_injective⟩ : ↥S ↪ V))
  have es : Finset.univ.map emb = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
      exact (slot (perm i)).property
    · intro hx
      let i := perm.symm (slot.symm ⟨x,hx⟩)
      refine Finset.mem_map.mpr ⟨i,Finset.mem_univ _,?_⟩
      simp [emb,i]
  have induced (i j : Fin 8) : (emb j ∈ neighbors C (emb i)) ↔ adj k i j=true :=
    (mem_neighbors C).trans (facts i j)
  refine ⟨⟨k,emb,es,?_,induced⟩⟩
  intro i
  have eq : (neighbors C w) ∩ (neighbors C (emb i)) =
      (neighbors C w).filter (fun x => x∈neighbors C (emb i)) := by ext x; simp
  rw [ambientCodeg,eq]
  change (S.filter (fun x => x∈neighbors C (emb i))).card = deg k i
  rw [←es,Finset.filter_map,Finset.card_map]
  simp_rw [Function.comp_apply,induced]
  exact atlas_row_degree k i

#print axioms atlas_host_transport
end Erdős151.H12
