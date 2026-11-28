import WagnerHostLinks
import HostIncidence

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]
  [DecidableEq V] [DecidableEq L] [DecidableEq R]
variable {E : L ↪ Finset V} {Tr : R ↪ Finset V}

namespace HostWagnerLinks
set_option linter.unusedSectionVars false

def nearTriangles (E : L ↪ Finset V) (Tr : R ↪ Finset V) (e : L) : Finset R :=
  Finset.univ.filter (fun t => E e ⊆ Tr t)

def spokesInTriangle (E : L ↪ Finset V) (Tr : R ↪ Finset V) (t : R) : Finset L :=
  Finset.univ.filter (fun e => E e ⊆ Tr t)

/-- Standard model link correctness on pairs of distinct link vertices. -/
def Reflects (w : HostWagnerLinks E Tr) : Prop :=
  ∀ v i j, i ≠ j →
    hostRel E ((w.slot v i).val) ((w.slot v j).val) → WagnerFin8.Adj i j

/-- Every pair of distinct vertices of every supplied triangle is a host edge. -/
def TrianglesClosed (E : L ↪ Finset V) (Tr : R ↪ Finset V) : Prop :=
  ∀ t x y, x≠y → x∈Tr t → y∈Tr t → hostRel E x y

theorem adjacent_triangle_contains (w : HostWagnerLinks E Tr) (ec : ∀ e,(E e).card=2)
    (v : V) (i j : Fin 8) (ij : WagnerFin8.Adj i j) :
    ∃ t, E (w.spoke v i) ⊆ Tr t ∧ E (w.spoke v j) ⊆ Tr t := by
  obtain ⟨t,ht⟩ := w.triangle v i j ij
  refine ⟨t,?_,?_⟩
  · rw [w.spoke_set ec,ht]
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
    exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))
  · rw [w.spoke_set ec,ht]
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
    exact hz.elim Or.inl (fun h => Or.inr (Or.inr h))

theorem three_triangles_per_edge (w : HostWagnerLinks E Tr)
    (reflect : w.Reflects) (cl : TrianglesClosed E Tr)
    (ec : ∀ e,(E e).card=2) (tc : ∀ t,(Tr t).card=3) (e : L) :
    (nearTriangles E Tr e).card = 3 := by
  classical
  have en : (E e).Nonempty := Finset.card_pos.mp (by rw [ec]; decide)
  obtain ⟨v,hv⟩ := en
  obtain ⟨i,hi⟩ := w.spoke_of_contains ec v e hv
  let U := (Finset.univ : Finset (Fin 8)).filter (WagnerFin8.Adj i)
  let x (j : Fin 8) := (w.slot v j).val
  have hE : E e = {v,x i} := by rw [← hi,w.spoke_set ec]
  have xx : Function.Injective x := fun a b h => (w.slot v).injective (Subtype.ext h)
  have xnv (j : Fin 8) : x j ≠ v := (w.slot v j).property.1
  have cN (j : ↥U) : ∃ t : R, Tr t = {v,x i,x j.val} :=
    w.triangle v i j.val (Finset.mem_filter.mp j.property).2
  choose tr htr using cN
  have hn (j : ↥U) : j.val ≠ i := by
    intro h
    have h' := (Finset.mem_filter.mp j.property).2
    have : WagnerFin8.Adj i i := h ▸ h'
    exact WagnerFin8.irreflexive i this
  have inj : Function.Injective tr := by
    intro a b h
    have H : x a.val ∈ ({v,x i,x b.val} : Finset V) := by
      rw [← htr b, ← h, htr a]
      simp
    simp only [Finset.mem_insert,Finset.mem_singleton] at H
    exact Subtype.ext (H.elim (fun z => (xnv _ z).elim)
      (fun z => z.elim (fun q => (hn a (xx q)).elim) (fun q => xx q)))
  let emp : ↥U ↪ R := ⟨tr,inj⟩
  have hmap : (Finset.univ : Finset ↥U).map emp = nearTriangles E Tr e := by
    ext t
    constructor
    · intro ht
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      change E e ⊆ Tr (tr j)
      rw [hE,htr j]
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
      exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))
    · intro ht
      have hsub := (Finset.mem_filter.mp ht).2
      have hx : x i ∈ Tr t := hsub (by simp [hE])
      have hv' : v ∈ Tr t := hsub hv
      have outside : ∃ y ∈ Tr t, y ∉ E e := by
        by_contra! h
        have c := Finset.card_le_card (show Tr t ⊆ E e from h)
        rw [ec,tc] at c
        omega
      obtain ⟨y,hy,hyn⟩ := outside
      have hyv : y ≠ v := fun h => hyn (h.symm ▸ hv)
      have hyx : y ≠ x i := fun h => hyn (h.symm ▸ (by simp [hE] : x i ∈ E e))
      let j := (w.slot v).symm ⟨y,hyv,cl t v y hyv.symm hv' hy⟩
      have hj : x j = y := congrArg Subtype.val ((w.slot v).apply_symm_apply _)
      have hij : i ≠ j := fun h => hyx (hj.symm.trans (h ▸ rfl))
      have rel : hostRel E (x i) (x j) := hj.symm ▸ (cl t (x i) y hyx.symm hx hy)
      let jj : ↥U := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,reflect v i j hij rel⟩⟩
      refine Finset.mem_map.mpr ⟨jj,Finset.mem_univ _,Tr.injective ?_⟩
      change Tr (tr jj) = Tr t
      rw [htr jj,show x jj.val=y from hj]
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl|rfl
        · exact hv'
        · exact hx
        · exact hy
      · rw [tc]
        simp [(xnv i).symm,hyv.symm,hyx.symm]
  rw [← hmap,Finset.card_map,Finset.card_univ,Fintype.card_coe]
  exact WagnerFin8.degree i

/-- The cubic-incidence right-degree API used by the matching theorem. -/
theorem degree_column (w : HostWagnerLinks E Tr)
    (reflect : w.Reflects) (cl : TrianglesClosed E Tr)
    (ec : ∀ e,(E e).card=2) (tc : ∀ t,(Tr t).card=3) :
    ∀ e, (∑ t : R, if e ∈ spokesInTriangle E Tr t then (1:ℕ) else 0) = 3 := by
  intro e
  rw [← w.three_triangles_per_edge reflect cl ec tc e]
  simp only [spokesInTriangle,Finset.mem_filter,Finset.mem_univ,true_and,nearTriangles,
    Finset.card_filter]

theorem local_coTriangle (w : HostWagnerLinks E Tr) (ec : ∀ e,(E e).card=2)
    (v : V) (e f : L) (he : v∈E e) (hf : v∈E f) :
    ∃ n, Erdős151.H12.Steps (coTriangle (spokesInTriangle E Tr)) n e f := by
  obtain ⟨i,hi⟩ := w.spoke_of_contains ec v e he
  obtain ⟨j,hj⟩ := w.spoke_of_contains ec v f hf
  have localpath := WagnerFin8.connected_after_two ∅ (by simp) i j (by simp) (by simp)
  have convert {a b : Fin 8} (p : Relation.ReflTransGen
      (fun x y => WagnerFin8.Adj x y ∧ x ∉ (∅ : Finset (Fin 8)) ∧ y ∉ (∅ : Finset (Fin 8))) a b) :
      ∃ n, Erdős151.H12.Steps (coTriangle (spokesInTriangle E Tr)) n (w.spoke v a) (w.spoke v b) := by
    induction p with
    | refl => exact ⟨0,Erdős151.H12.Steps.zero _⟩
    | tail h hstep ih =>
      obtain ⟨t,ht,ht'⟩ := w.adjacent_triangle_contains ec v _ _ hstep.1
      have rel : coTriangle (spokesInTriangle E Tr) _ _ := ⟨t,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht'⟩⟩
      obtain ⟨m,pm⟩ := ih
      exact Steps.concat pm (Erdős151.H12.Steps.more rel (Erdős151.H12.Steps.zero _))
  simpa only [hi,hj] using convert localpath

#print axioms three_triangles_per_edge
#print axioms degree_column
#print axioms local_coTriangle
end HostWagnerLinks
end Erdős151.H12.Wagner
