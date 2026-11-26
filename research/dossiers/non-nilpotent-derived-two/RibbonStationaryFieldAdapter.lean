import RibbonStationarySlopeFinalCore
import RibbonP11Adapters

namespace RibbonStationaryField
open RibbonStationaryWord RibbonStationaryChart RibbonP11
open RibbonAffine (eRow)
universe u v
variable {G : Type u} [Group G] {K : Type v} [Field K]

def FieldWords : Prop :=
  ∀ {L : Type v} [Field L] (a b : Lˣ) (n : Nat),
    (2:L)≠0 → Odd n → (¬3∣n) → a^n=1 → b^n=1 → a≠1 →
    (∃ k : Count, separates a b k) ∨ FieldResidual a b

theorem chart_cycle (dnil : RibbonDerivedTwo.D2 G) (x y : G)
    (μ : G→*Kˣ) (τ : G→K) (co : Aff μ τ) (tx : τ x=0) (ty : τ y=1)
    (k : Count) (S : separates (μ x) (μ y) k) :
    Good x y := by
  apply Or.inr ∘ Or.inr ∘ Or.inr
  apply from_state (RibbonP11Adapters.dnil dnil) k x y
    (fun i => eRow (μ x) (μ y) (symbol k i.val)) _ S
  intro i j E
  rw [←symbol_sound μ τ co x y tx ty k i.val,←symbol_sound μ τ co x y tx ty k j.val,E]

def Accepted (a b : F) : Prop :=
  (a=3 ∨ a=4 ∨ a=5 ∨ a=9) ∧ (b=1 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=9)
instance (a b : F) : Decidable (Accepted a b) := by unfold Accepted; infer_instance

private instance (z : F×F) : Decidable (RibbonP11Adapters.Bad z) := by
  unfold RibbonP11Adapters.Bad
  infer_instance

private theorem exact_bad (a b : F) (e : Accepted a b) : RibbonP11Adapters.Bad (a,b) ∨
    ∃ k : Fin 8, a=(extra k).1.val ∧ b=(extra k).2.1.val := by
  have h : ∀ c d : F, Accepted c d →
      RibbonP11Adapters.Bad (c,d) ∨ ∃ k : Fin 8, c=(extra k).1.val ∧ d=(extra k).2.1.val :=
    by decide +kernel
  exact h a b e

private theorem flip_bad (a b : F) :
    RibbonP11Adapters.Bad (a,b) → RibbonP11Adapters.Bad (b,a) := by
  have e : ∀ a b : F, RibbonP11Adapters.Bad (a,b) → RibbonP11Adapters.Bad (b,a) :=
    by decide +kernel
  exact e a b

private theorem values_a (f : F→+*K) (a : Kˣ)
    (A : (a:K)=3 ∨ (a:K)=4 ∨ (a:K)=5 ∨ (a:K)=9) :
    ∃ z : F, f z=(a:K) ∧ (z=3 ∨ z=4 ∨ z=5 ∨ z=9) := by
  rcases A with A|A|A|A
  · exact ⟨3,by rw [show (3:F)=((3:Nat):F) by decide,map_natCast]; exact A.symm,Or.inl rfl⟩
  · exact ⟨4,by rw [show (4:F)=((4:Nat):F) by decide,map_natCast]; exact A.symm,Or.inr (Or.inl rfl)⟩
  · exact ⟨5,by rw [show (5:F)=((5:Nat):F) by decide,map_natCast]; exact A.symm,Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨9,by rw [show (9:F)=((9:Nat):F) by decide,map_natCast]; exact A.symm,Or.inr (Or.inr (Or.inr rfl))⟩

private theorem values_b (f : F→+*K) (b : Kˣ)
    (B : (b:K)=1 ∨ (b:K)=3 ∨ (b:K)=4 ∨ (b:K)=5 ∨ (b:K)=9) :
    ∃ z : F, f z=(b:K) ∧ (z=1 ∨ z=3 ∨ z=4 ∨ z=5 ∨ z=9) := by
  rcases B with B|B
  · exact ⟨1,by simpa using B.symm,Or.inl rfl⟩
  · obtain ⟨z,E,W⟩ := values_a f b B
    exact ⟨z,E,Or.inr W⟩

private theorem residual_or_separates (a b : Kˣ) (H : FieldResidual a b) :
    (∃ k, separates a b k) ∨ ∃ (e : F→+*K) (x y : F),
      e x=(a:K) ∧ e y=(b:K) ∧ RibbonP11Adapters.Bad (x,y) := by
  obtain ⟨p,_,A,B⟩ := H
  letI : CharP K 11 := (CharP.charP_iff_prime_eq_zero (R:=K) (by decide : Nat.Prime 11)).mpr p
  let f : F →+* K := ZMod.castHom (dvd_refl 11) K
  obtain ⟨x,Ex,Hx⟩ := values_a f a A
  obtain ⟨y,Ey,Hy⟩ := values_b f b B
  rcases exact_bad x y ⟨Hx,Hy⟩ with bad|⟨k,X,Y⟩
  · exact Or.inr ⟨f,x,y,Ex,Ey,bad⟩
  · refine Or.inl ⟨(extra k).2.2,extra_separates a b p k ?_ ?_⟩
    · rw [X,←ZMod.natCast_zmod_val (extra k).1.val,map_natCast] at Ex
      exact Ex.symm
    · rw [Y,←ZMod.natCast_zmod_val (extra k).2.1.val,map_natCast] at Ey
      exact Ey.symm

theorem field_adapter (word_cert : FieldWords.{v}) : FieldCover.{u,v} RibbonP11Adapters.Bad := by
  intro G K _ _ _ _ m x y μ τ two odd no3 co normal
  have pn (g : G) : (μ g)^(Nat.card G)=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_map_dvd μ g) (orderOf_dvd_natCard g))
  rcases normal with ⟨nz,x0,y1⟩|⟨_,nz,x1,y0⟩
  · have xN : μ x≠1 := fun z => nz (by simp [z])
    rcases word_cert (μ x) (μ y) (Nat.card G) two odd no3 (pn x) (pn y) xN with
      ⟨k,S⟩|R
    · exact Or.inl (chart_cycle m _ _ μ τ co x0 y1 k S)
    · rcases residual_or_separates _ _ R with ⟨k,S⟩ | E
      · exact Or.inl (chart_cycle m _ _ μ τ co x0 y1 k S)
      · exact Or.inr E
  · have yN : μ y≠1 := fun z => nz (by simp [z])
    have C : (∃ k : Count, separates (μ y) (μ x) k) ∨ FieldResidual (μ y) (μ x) :=
      word_cert (μ y) (μ x) (Nat.card G) two odd no3 (pn y) (pn x) yN
    have flip : Good y x → Good x y := fun h =>
      h.imp RibbonP3.flip_cycle (fun h => h.imp RibbonP3.flip_cycle (fun h =>
        h.imp RibbonP3.flip_cycle (fun h => h.imp RibbonP3.flip_cycle RibbonP3.flip_cycle)))
    rcases C with ⟨k,S⟩|R
    · exact Or.inl (flip (chart_cycle m _ _ μ τ co y0 x1 k S))
    · rcases residual_or_separates _ _ R with ⟨k,S⟩ | ⟨f,a,b,A,B,H⟩
      · exact Or.inl (flip (chart_cycle m _ _ μ τ co y0 x1 k S))
      · exact Or.inr ⟨f,b,a,B,A,flip_bad a b H⟩

end RibbonStationaryField
#print axioms RibbonStationaryField.field_adapter
