import LubellCylinder

namespace IU.Lubell

theorem same_card_inter {A B : Finset Nat} {k : Nat}
    (a : A.card=k+1) (b : B.card=k+1) (ne : A≠B) (lo : k≤(A∩B).card) :
    (A∩B).card=k := by
  have z : (A∩B).card<A.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left,?_⟩
    intro e
    have sub : A⊆B := e ▸ Finset.inter_subset_right
    exact ne (Finset.eq_of_subset_of_card_le sub (by omega))
  omega

theorem johnson_star_top {F : Family} {k : Nat}
    (layer : ∀ A∈F, A.card=k+1)
    (pair : ∀ A∈F, ∀ B∈F, k≤(A∩B).card)
    (nontrivial : 1<F.card) :
    (∃ T, T.card=k ∧ ∀ A∈F, T⊆A) ∨
      (∃ U, U.card=k+2 ∧ ∀ A∈F, A⊆U) := by
  obtain ⟨X,xF,Y,yF,ne⟩ := Finset.one_lt_card.mp nontrivial
  let C := X∩Y
  let U := X∪Y
  have c : C.card=k := same_card_inter (layer X xF) (layer Y yF) ne (pair X xF Y yF)
  have u : U.card=k+2 := by
    have J := Finset.card_union_add_card_inter X Y
    change U.card+C.card=X.card+Y.card at J
    have a := layer X xF
    have b := layer Y yF
    omega
  by_cases T : ∀ A∈F, C⊆A
  · exact Or.inl ⟨C,c,T⟩
  have embed (A : Finset Nat) (aF : A∈F) (notC : ¬C⊆A) : A⊆U := by
    have lc : (A∩C).card<k := by
      rw [←c]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,?_⟩
      intro eq
      exact notC (eq ▸ Finset.inter_subset_left)
    have H := Finset.card_union_add_card_inter (A∩X) (A∩Y)
    have eu : (A∩X)∪(A∩Y)=A∩U := by
      ext i
      simp only [U,Finset.mem_union,Finset.mem_inter]
      tauto
    have ec : (A∩X)∩(A∩Y)=A∩C := by
      ext i
      simp only [C,Finset.mem_inter]
      tauto
    rw [eu,ec] at H
    have hX := pair A aF X xF
    have hY := pair A aF Y yF
    have a := layer A aF
    have E := Finset.eq_of_subset_of_card_le (show A∩U ⊆ A from Finset.inter_subset_left) (by omega)
    exact E ▸ Finset.inter_subset_right
  push Not at T
  obtain ⟨Z,zF,zNot⟩ := T
  have zU := embed Z zF zNot
  refine Or.inr ⟨U,u,?_⟩
  intro A aF
  by_cases aC : C⊆A
  · by_contra aU
    have cU : C⊆U := Finset.inter_subset_left.trans (Finset.subset_union_left)
    have E : A∩U=C := by
      symm
      apply Finset.eq_of_subset_of_card_le (show C⊆A∩U from fun x hx => Finset.mem_inter.mpr ⟨aC hx,cU hx⟩)
      have a := layer A aF
      have z : (A∩U).card<A.card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,?_⟩
        intro e
        exact aU (e ▸ Finset.inter_subset_right)
      omega
    have zloss : (Z∩C).card<k := by
      rw [←c]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,?_⟩
      intro eq
      exact zNot (eq ▸ Finset.inter_subset_left)
    have az : A∩Z ⊆ Z∩C := by
      intro x xm
      obtain ⟨xa,xz⟩ := Finset.mem_inter.mp xm
      refine Finset.mem_inter.mpr ⟨xz,?_⟩
      rw [←E]
      exact Finset.mem_inter.mpr ⟨xa,zU xz⟩
    have N := Finset.card_le_card az
    have B := pair A aF Z zF
    omega
  · exact embed A aF aC

theorem count_above {T U : Finset Nat} {F : Family} {k : Nat}
    (tc : T.card=k) (weight : ∀ A∈F, A.card=k+1)
    (lo : ∀ A∈F, T⊆A) (hi : ∀ A∈F, A⊆U) :
    F.card ≤ (U\T).card := by
  classical
  let f := fun A : Finset Nat => A\T
  have inj : Set.InjOn f ↑F := by
    intro A a B b e
    have eq (A : Finset Nat) (h : A∈F) : f A ∪ T = A := Finset.sdiff_union_of_subset (lo A h)
    rw [←eq A a,←eq B b,e]
  have h : F.image f ⊆ (U\T).powersetCard 1 := by
    intro X hm
    obtain ⟨A,a,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff (hi A a) (fun _ h=>h),?_⟩
    rw [show f A=A\T from rfl,Finset.card_sdiff_of_subset (lo A a),weight A a,tc]
    omega
  have d := Finset.card_le_card h
  rw [Finset.card_image_of_injOn inj,Finset.card_powersetCard,Nat.choose_one_right] at d
  exact d

theorem count_below {U : Finset Nat} {F : Family} {k : Nat}
    (uc : U.card=k+2) (weight : ∀ A∈F, A.card=k+1)
    (hi : ∀ A∈F, A⊆U) : F.card ≤ k+2 := by
  classical
  let f := fun A : Finset Nat => U\A
  have inj : Set.InjOn f ↑F := by
    intro A a B b e
    have eq (A : Finset Nat) (h : A∈F) : U\f A = A := by
      ext j
      simp only [f,Finset.mem_sdiff]
      have h : j∈A → j∈U := fun hJ => hi A h hJ
      tauto
    rw [←eq A a,←eq B b,e]
  have h : F.image f ⊆ U.powersetCard 1 := by
    intro X hm
    obtain ⟨A,a,rfl⟩ := Finset.mem_image.mp hm
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset,?_⟩
    rw [show f A=U\A from rfl,Finset.card_sdiff_of_subset (hi A a),weight A a,uc]
    omega
  have d := Finset.card_le_card h
  rw [Finset.card_image_of_injOn inj,Finset.card_powersetCard,Nat.choose_one_right,uc] at d
  exact d

#print axioms johnson_star_top
end IU.Lubell
