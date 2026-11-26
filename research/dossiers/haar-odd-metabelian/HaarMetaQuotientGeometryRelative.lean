import HaarMetaQuotientGeometry

namespace HaarMetaQuotientGeometry
variable {Q : Type*} [AddCommGroup Q]

theorem span_proj (t z : Q) (h : Spans z t) :
    AddSubgroup.zmultiples (proj t z) = ⊤ := by
  have h' := congrArg (fun S : AddSubgroup Q => S.map (proj t)) h
  change (AddSubgroup.closure ({z,t} : Set Q)).map (proj t) = (⊤ : AddSubgroup Q).map (proj t) at h'
  have surj : Function.Surjective (proj t) := QuotientAddGroup.mk'_surjective _
  rw [AddMonoidHom.map_closure,Set.image_pair,projected_t,
    AddSubgroup.map_top_of_surjective (proj t) surj] at h'
  exact cyclic_of_mem _ 0 (proj t z) h' (AddSubgroup.mem_zmultiples _) (AddSubgroup.zero_mem _)

theorem card_cyclic (z : Q) (hz : AddSubgroup.zmultiples z=⊤) :
    Nat.card Q = addOrderOf z := by
  rw [← Nat.card_zmultiples, hz]
  exact (Nat.card_congr AddSubgroup.topEquiv.toEquiv).symm

theorem relativeOrder_eq_card (t z : Q) (gen : Spans z t) :
    relativeOrder t z = Nat.card (Q ⧸ AddSubgroup.zmultiples t) :=
  (card_cyclic (proj t z) (span_proj t z gen)).symm

theorem relative_card (t z : Q) (gen : Spans z t) (ht : addOrderOf t=3) :
    Nat.card Q = 3*relativeOrder t z := by
  rw [relativeOrder_eq_card t z gen, Nat.mul_comm]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples t),
    Nat.card_zmultiples, ht]

theorem relative_pos [Finite Q] (t z : Q) : 0<relativeOrder t z :=
  (isOfFinAddOrder_of_finite (proj t z)).addOrderOf_pos

theorem relative_odd (t z : Q) (gen : Spans z t) (odd : Odd (Nat.card Q)) :
    Odd (relativeOrder t z) := by
  rw [relativeOrder_eq_card _ _ gen]
  exact Odd.of_dvd_nat odd (AddSubgroup.card_quotient_dvd_card _)

theorem small_relative [Finite Q] (t z : Q) (gen : Spans z t)
    (odd : Odd (Nat.card Q)) (small : relativeOrder t z < 6) :
    relativeOrder t z=1 ∨ relativeOrder t z=3 ∨ relativeOrder t z=5 := by
  have p := relative_pos t z
  obtain ⟨k,hk⟩ := relative_odd t z gen odd
  omega

theorem first_cylinder_cases [Finite Q] (x y : Q) (gen : Spans x y)
    (odd : Odd (Nat.card Q)) (hx : x≠0) (h3 : (3:ℕ) • x=0) :
    (4≤relativeOrder x y ∧ Function.Injective (cylinder x y 4)) ∨
    (relativeOrder x y=1 ∧ Nat.card Q=3) ∨
    (relativeOrder x y=3 ∧ Nat.card Q=9) := by
  have ord := torsion_three x hx h3
  have gens := span_swap _ _ gen
  have card := relative_card x y gens ord
  by_cases h : 4≤relativeOrder x y
  · exact Or.inl ⟨h,cylinder_injective _ _ _ ord h⟩
  · rcases small_relative x y gens odd (by omega) with e|e|e
    · exact Or.inr (Or.inl ⟨e,by omega⟩)
    · exact Or.inr (Or.inr ⟨e,by omega⟩)
    · omega

theorem second_cylinder_cases [Finite Q] (x y : Q) (gen : Spans x y)
    (odd : Odd (Nat.card Q))
    (hne : y-(2:ℤ) • x ≠ 0) (h3 : (3:ℕ) • (y-(2:ℤ) • x)=0) :
    let t := y-(2:ℤ) • x
    (6≤relativeOrder t x ∧ Function.Injective (cylinder t x 6)) ∨
    (relativeOrder t x=1 ∧ Nat.card Q=3) ∨
    (relativeOrder t x=3 ∧ Nat.card Q=9) ∨
    (relativeOrder t x=5 ∧ Nat.card Q=15) := by
  let t := y-(2:ℤ) • x
  have ord := torsion_three t hne h3
  have gens := span_shear x y 2 gen
  have card := relative_card t x gens ord
  by_cases h : 6≤relativeOrder t x
  · exact Or.inl ⟨h,cylinder_injective _ _ _ ord h⟩
  · rcases small_relative t x gens odd (by omega) with e|e|e
    · exact Or.inr (Or.inl ⟨e,by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e,by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e,by omega⟩))

theorem spans_of_same_card_zmultiple [Finite Q] (z : Q) (hz : addOrderOf z=Nat.card Q) :
    AddSubgroup.zmultiples z=⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  exact (Nat.card_zmultiples z).trans hz

theorem order_nine_split [Finite Q] (t z : Q) (gen : Spans z t)
    (ht : addOrderOf t=3) (hrel : relativeOrder t z=3) :
    AddSubgroup.zmultiples z=⊤ ∨
      ((3:ℕ) • z=0 ∧ Function.Bijective (cylinder t z 3)) := by
  have card : Nat.card Q=9 := (relative_card t z gen ht).trans (by omega)
  by_cases hz : (3:ℕ) • z=0
  · refine Or.inr ⟨hz,(Nat.bijective_iff_injective_and_card _).mpr ⟨cylinder_injective _ _ _ ht hrel.ge, ?_⟩⟩
    simp [card]
  · have hzD := addOrderOf_dvd_natCard z
    have hpos := (isOfFinAddOrder_of_finite z).addOrderOf_pos
    have h9 : addOrderOf z=9 := by
      let d := addOrderOf z
      change d ∣ Nat.card Q at hzD
      rw [card] at hzD
      have d3 : ¬ d ∣ 3 := fun h => hz (addOrderOf_dvd_iff_nsmul_eq_zero.mp h)
      have ho : ∀ d : Fin 10, (d.val ∣ 9) → ¬ (d.val ∣ 3) → d.val=9 := by decide
      exact ho ⟨d,by have e := Nat.le_of_dvd (by decide : 0 < (9:ℕ)) hzD; omega⟩ hzD d3
    exact Or.inl (spans_of_same_card_zmultiple z (h9.trans card.symm))

theorem order_fifteen_cyclic [Finite Q] (t z : Q) (gen : Spans z t)
    (ht : addOrderOf t=3) (hrel : relativeOrder t z=5) :
    ∃ q : Q, AddSubgroup.zmultiples q=⊤ := by
  have card : Nat.card Q=15 := (relative_card t z gen ht).trans (by omega)
  have hzD := addOrderOf_dvd_natCard z
  have mod : 5 ∣ addOrderOf z := by
    have h : (addOrderOf z) • proj t z = 0 := by rw [←map_nsmul,addOrderOf_nsmul_eq_zero,map_zero]
    have dv := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
    change relativeOrder t z ∣ addOrderOf z at dv
    simpa [hrel] using dv
  have hor : addOrderOf z=5 ∨ addOrderOf z=15 := by
    let d := addOrderOf z
    change d ∣ Nat.card Q at hzD
    rw [card] at hzD
    have ho : ∀ d : Fin 16, (d.val ∣ 15) → (5 ∣ d.val) → d.val=5 ∨ d.val=15 := by decide
    exact ho ⟨d,by have e := Nat.le_of_dvd (by decide : 0 < (15:ℕ)) hzD; omega⟩ hzD mod
  rcases hor with e|e
  · refine ⟨z+t, spans_of_same_card_zmultiple _ ?_⟩
    have hco : Nat.Coprime (addOrderOf z) (addOrderOf t) := by rw [e,ht]; decide
    rw [(AddCommute.all z t).addOrderOf_add_eq_mul_addOrderOf_of_coprime hco, e,ht,card]
  · exact ⟨z,spans_of_same_card_zmultiple _ (e.trans card.symm)⟩

end HaarMetaQuotientGeometry

#print axioms HaarMetaQuotientGeometry.first_cylinder_cases
#print axioms HaarMetaQuotientGeometry.second_cylinder_cases
#print axioms HaarMetaQuotientGeometry.order_nine_split
#print axioms HaarMetaQuotientGeometry.order_fifteen_cyclic
