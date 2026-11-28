import CubicSquareCertificate

open scoped BigOperators
namespace Erdős151.H12.Wagner

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def indexRange {I W : Type*} [Fintype I] [DecidableEq W]
    (f : I → W) (inj : Function.Injective f) : I ≃ ↥(Finset.univ.image f) :=
  Equiv.ofBijective (fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => inj (congrArg Subtype.val h),fun ⟨_,h⟩ => by
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨i,rfl⟩⟩

@[simp] theorem indexRange_val {I W : Type*} [Fintype I] [DecidableEq W]
    (f : I → W) (inj : Function.Injective f) (i : I) :
    (indexRange f inj i).val = f i := rfl

/-- The local data of an alternating 8-cycle in cubic incidence
form: four spokes, four triangles, four distinct outside third edges.
The cut certificate and co-triangle connectivity may be supplied directly
by any host-graph representation. -/
theorem cubic_coloring_of_ordered_square
    (edge : E → Finset V)
    (row : ∀ e, (∑ v : V, if v ∈ edge e then (1:ℕ) else 0) = 3)
    (col : ∀ v, (∑ e : E, if v ∈ edge e then (1:ℕ) else 0) = 3)
    (spoke : Fin 4 → V) (tr : Fin 4 → E) (outside : Fin 4 → V)
    (si : Function.Injective spoke) (ti : Function.Injective tr) (oi : Function.Injective outside)
    (shape : ∀ i, edge (tr i) = {spoke i,spoke (i+1),outside i})
    (small : ∀ S : Finset V, ∀ T : Finset E,
      Disjoint S (Finset.univ.image spoke) → 3 ≤ S.card →
        cutMass (fun v e => v∈edge e) S T ≤ 5 →
        mass (fun v e => v∈edge e) S T < S.card + T.card)
    (connected : ∀ v, ∃ n, Erdős151.H12.Steps (coTriangle edge) n v (spoke 0)) :
    ∃ c : V → Bool, ∀ e, Mixed c (edge e) := by
  classical
  let P := Finset.univ.image spoke
  let B := Finset.univ.image tr
  let ie := indexRange spoke si
  let it := indexRange tr ti
  let m0 : ↥P ≃ ↥B := ie.symm.trans it
  have h4 : B.card = 4 := by
    change (Finset.univ.image tr).card = 4
    rw [Finset.card_image_of_injective _ ti, Finset.card_univ, Fintype.card_fin]
  have vp (i : Fin 4) : spoke i ∈ P := (ie i).property
  have orig (v : ↥P) : spoke (ie.symm v) = v.val := by
    exact congrArg Subtype.val (ie.apply_symm_apply v)
  have bm (v : ↥P) : (m0 v).val = tr (ie.symm v) := rfl
  let unitColor : Fin 4 → Bool := fun i => decide (i.val % 2 = 0)
  have stepColor : ∀ i, unitColor i ≠ unitColor (i+1) := by decide
  have stepNe : ∀ i:Fin 4, i ≠ i+1 := by decide
  let base (v : V) : Bool := if h : v∈P then unitColor (ie.symm ⟨v,h⟩) else false
  have baseAt (v : ↥P) : base v.val = unitColor (ie.symm v) := by
    simp [base,v.property]
  have rest (s : V) (h : s∉P) {i : Fin 4} (hs : s ∈ edge (tr i)) : s=outside i := by
    rw [shape] at hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with he|he|he
    · exact False.elim (h (he.symm ▸ vp i))
    · exact False.elim (h (he.symm ▸ vp (i+1)))
    · exact he
  refine cubic_coloring_of_square_certificate edge row col P B h4 m0 ?localM ?left ?right small
    (spoke 0) (vp 0) connected base ?alt
  case localM =>
    intro v
    rw [bm,shape,← orig v]
    simp
  case left =>
    intro s hs t ht u hu st su
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hu
    exact congrArg tr (oi ((rest s hs st).symm.trans (rest s hs su)))
  case right =>
    intro t ht s hs u hu st su
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact (rest s hs st).trans (rest u hu su).symm
  case alt =>
    intro v
    let i := ie.symm v
    let w := ie (i+1)
    refine ⟨w,?_ ,?_,?_⟩
    · intro q
      have e : spoke i = spoke (i+1) := (orig v).trans q
      exact stepNe i (si e)
    · rw [bm,shape]
      simp [w,i,ie]
    · rw [baseAt v,baseAt w]
      simpa [w,i] using stepColor i

#print axioms cubic_coloring_of_ordered_square
end Erdős151.H12.Wagner
