import HaarMetaQuotientGeometryRelative
namespace HaarMetaQuotientGeometry
variable {Q : Type*} [AddCommGroup Q]

theorem zmodThree_nsmul_add (x : Q) (hx : addOrderOf x=3) (a b : ZMod 3) :
    (a+b).val • x = a.val • x+b.val • x := by
  rw [ZMod.val_add,←add_nsmul]
  simpa only [hx] using (mod_addOrderOf_nsmul x (a.val+b.val))

def torus (t z : Q) (ht : addOrderOf t=3) (hz : addOrderOf z=3) :
    (ZMod 3 × ZMod 3) →+ Q where
  toFun p := p.1.val • z+p.2.val • t
  map_zero' := by simp
  map_add' a b := by
    change (a.1+b.1).val • z+(a.2+b.2).val • t =
      (a.1.val • z+a.2.val • t)+(b.1.val • z+b.2.val • t)
    rw [zmodThree_nsmul_add z hz,zmodThree_nsmul_add t ht]
    abel

noncomputable def torusCoordinates [Finite Q] (t z : Q) (ht : addOrderOf t=3)
    (gen : Spans z t) (rel : relativeOrder t z=3) (hz : addOrderOf z=3) :
    ZMod 3 × ZMod 3 ≃+ Q := by
  apply AddEquiv.ofBijective (torus t z ht hz)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,?_⟩
  · intro a b h
    let fa : Fin 3 × Fin 3 := (⟨a.1.val,ZMod.val_lt _⟩,⟨a.2.val,ZMod.val_lt _⟩)
    let fb : Fin 3 × Fin 3 := (⟨b.1.val,ZMod.val_lt _⟩,⟨b.2.val,ZMod.val_lt _⟩)
    have e : fa=fb := cylinder_injective t z 3 ht rel.ge (show cylinder t z 3 fa=cylinder t z 3 fb from h)
    apply Prod.ext
    · have e' := congrArg (fun a : Fin 3 × Fin 3 => a.1.val) e
      simpa [fa,fb] using congrArg (fun n : ℕ => (n:ZMod 3)) e'
    · have e' := congrArg (fun a : Fin 3 × Fin 3 => a.2.val) e
      simpa [fa,fb] using congrArg (fun n : ℕ => (n:ZMod 3)) e'
  · have c : Nat.card (ZMod 3)=3 := by rw [Nat.card_eq_fintype_card,ZMod.card]
    rw [Nat.card_prod,c,relative_card t z gen ht,rel]

theorem order_nine_structured [Finite Q] (t z : Q) (ht : addOrderOf t=3)
    (gen : Spans z t) (rel : relativeOrder t z=3) :
    AddSubgroup.zmultiples z=⊤ ∨
      ∃ hz : addOrderOf z=3, Nonempty (ZMod 3 × ZMod 3 ≃+ Q) := by
  rcases order_nine_split t z gen ht rel with h|⟨hz,_⟩
  · exact Or.inl h
  · have zne : z≠0 := by
      intro e
      simp [relativeOrder,e, map_zero] at rel
    have ord : addOrderOf z=3 := torsion_three z zne hz
    exact Or.inr ⟨ord,⟨torusCoordinates t z ht gen rel ord⟩⟩

end HaarMetaQuotientGeometry

#print axioms HaarMetaQuotientGeometry.torusCoordinates
