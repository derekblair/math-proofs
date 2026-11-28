import N63CoreTight
import N63TenActual

namespace Erdos151H13
open scoped BigOperators
open Erdős151 Erdos151H12 Erdos151CoreHigh Erdős151.H12
open Finset NineLinkPivot

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G C : V → V → Prop) [DecidableRel G] [DecidableRel C]

theorem certified_tight_core63
    (sym : ∀ {a b}, G a b → G b a) (irr : ∀ a, ¬G a a) (link : TriangleFreeLinks G)
    (R41 : ∀ n, 41 ≤ n → Erdős151.H10.TriangleIndependentTen (Fin n))
    (sub : BikovLocal.Sub C G) (cs : BikovLocal.Sym C) (ci : BikovLocal.Loopless C)
    (ct : BikovLocal.TriangleFreeLinks C) (cr : BikovLocal.Ramsey C)
    (minimal : ∀ H : V→V→Prop, BikovLocal.Sub H C → BikovLocal.Sym H →
      ∀ a b, C a b → ¬H a b → ¬BikovLocal.Ramsey H)
    (coreMin : ∀ v, (neighbors C v).Nonempty → 8 ≤ (neighbors C v).card)
    (two : TwoTriangles C)
    (max12 : ∀ v, (neighbors G v).card ≤12) (size63 : 63 ≤ Fintype.card V)
    (noFree : ¬ ∃ T : Finset V, 13 ≤ T.card ∧ Free (Forbidden G) (T : Set V)) :
    ∀ v, (neighbors C v).Nonempty →
      (∃ L : NamedLink (neighbors C) (ambientCodeg C) v,
          (Erdos151MarkedLinkTable.edges L.kind).length=12) ∨
      ((neighbors C v).card=10 ∧ (neighbors G v).card=12 ∧
        ∀ a ∈ neighbors C v, deg C (neighbors C v) a=3) := by
  apply order63_tight_core G C sym irr link R41 sub cs ci ct cr minimal coreMin two max12 size63 noFree
  intro w r10 density high
  let S := neighbors C w
  have eq (x : ↥S) : Erdos151N63.fullDeg (tenAdj G C w) x = deg G S x.val :=
    fullDeg_near_subtype G S x
  have rel (x : ↥S) : G w x.val := sub ((mem_neighbors C).mp x.property)
  have tf (x y z : ↥S) (xy : tenAdj G C w x y) (xz : tenAdj G C w x z) :
      ¬tenAdj G C w y z :=
    fun yz => link w x.val y.val z.val (rel x) (rel y) (rel z) xy yz xz
  have mn (i : ↥S) : 2 ≤ Erdos151N63.fullDeg (tenAdj G C w) i := by
    rw [eq]
    obtain ⟨a,b,ab,wa,ia,wb,ib⟩ := two w i.val ((mem_neighbors C).mp i.property)
    exact one_lt_card.mpr ⟨a,mem_filter.mpr ⟨(mem_neighbors C).mpr wa,sub ia⟩,
      b,mem_filter.mpr ⟨(mem_neighbors C).mpr wb,sub ib⟩,ab⟩
  have den : 30 ≤ ∑ a : ↥S, Erdos151N63.fullDeg (tenAdj G C w) a := by
    change 30 ≤ ∑ a ∈ S.attach, Erdos151N63.fullDeg (tenAdj G C w) a
    simp only [eq,Finset.sum_attach]
    exact density
  have hi : ∃ a : ↥S, 4≤Erdos151N63.fullDeg (tenAdj G C w) a := by
    obtain ⟨a,ha,ah⟩ := high
    exact ⟨⟨a,ha⟩,(eq ⟨a,ha⟩).symm ▸ ah⟩
  have sz : Fintype.card ↥S=10 := by simpa using r10
  have wit := Erdos151N63.noncubic_ten_witness (tenAdj G C w) sz (fun _ _ => ⟨sym,sym⟩)
    (fun x => irr x.val) tf mn den hi
  have nl (a b : V) (ab : C a b) : ¬Lone G a b := by
    obtain ⟨x,_,_,ax,bx,_,_⟩ := two a b ab
    exact fun h => h.2 x ⟨sub ax,sub bx⟩
  exact noFree (free13_of_ten_witness G C w r10 wit sym irr link R41
    (fun _ _ h=>sub h) (fun {_ _} h=>cs h) nl
    (fun x wx => coreMin x ⟨w,(mem_neighbors C).mpr (cs wx)⟩) max12 size63)

#print axioms certified_tight_core63
end Erdos151H13
