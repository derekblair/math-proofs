import RibbonAllOddExtras
import RibbonAllOddResidual
import RibbonOddLabels
import RibbonStationaryWords

namespace RibbonAllOddField
open RibbonStationaryChart RibbonP11 RibbonOdd RibbonOddFinite RibbonDerived3
open scoped commutatorElement
open RibbonAffine (eRow)
universe u v
variable {G : Type u} [Group G] {K : Type v} [Field K]

def FieldWords : Prop :=
  ∀ {L : Type v} [Field L] (a b : Lˣ) (n : Nat),
    (2:L)≠0 → Odd n → a^n=1 → b^n=1 → a≠1 →
    (∃ k : Count, separates a b k) ∨ FieldResidual a b

private theorem dnil_of_d2 (m : RibbonDerivedTwo.D2 G) : DLS G 2=⊥ := by
  apply le_bot_iff.mp
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  exact Subgroup.mem_bot.mpr (RibbonStationaryWords.central m ha hb).commutator_eq

theorem chart_cycle (dnil : RibbonDerivedTwo.D2 G) (x y : G)
    (μ : G→*Kˣ) (τ : G→K) (co : Aff μ τ) (tx : τ x=0) (ty : τ y=1)
    (k : Count) (S : separates (μ x) (μ y) k) :
    Good x y := by
  apply Or.inr ∘ Or.inr ∘ Or.inr
  apply from_state (dnil_of_d2 dnil) k x y
    (fun i => eRow (μ x) (μ y) (symbol k i.val)) _ S
  intro i j E
  rw [←symbol_sound μ τ co x y tx ty k i.val,←symbol_sound μ τ co x y tx ty k j.val,E]

def rawList : List Triple :=
  [(7,2,1),(7,2,2),(7,2,4),(7,4,1),(7,4,2),(7,4,4),
    (11,3,1),(11,3,3),(11,3,4),(11,3,5),(11,3,9),
    (11,4,1),(11,4,3),(11,4,4),(11,4,5),(11,4,9),
    (11,5,1),(11,5,3),(11,5,4),(11,5,5),(11,5,9),
    (11,9,1),(11,9,3),(11,9,4),(11,9,5),(11,9,9),
    (13,3,1),(13,3,3),(13,3,9),(13,9,1),(13,9,3),(13,9,9),
    (43,31,1)]

theorem raw_mem (p a b : Nat) (R : Raw p a b) : (p,a,b)∈rawList := by
  rcases R with ⟨rfl,A,B⟩|⟨rfl,A,B⟩|⟨rfl,A,B⟩|⟨rfl,rfl,rfl⟩
  · rcases A with rfl|rfl <;> rcases B with rfl|rfl|rfl <;> decide
  · rcases A with rfl|rfl|rfl|rfl <;> rcases B with rfl|rfl|rfl|rfl|rfl <;> decide
  · rcases A with rfl|rfl <;> rcases B with rfl|rfl|rfl <;> decide
  · decide

private instance (r : Triple) : Decidable (Bad r) := by unfold Bad; infer_instance
private instance (p : Nat) : Decidable (PrimeBad p) := by unfold PrimeBad; infer_instance

def ExtraOrBad (r : Triple) : Prop :=
  (Bad r ∧ PrimeBad r.1 ∧ r.2.1<r.1 ∧ r.2.2<r.1) ∨
  ∃ i : Fin 13, r=((extraCases i).1,(extraCases i).2.1,(extraCases i).2.2.1)
instance (r : Triple) : Decidable (ExtraOrBad r) := by unfold ExtraOrBad; infer_instance

theorem classify (p a b : Nat) (R : Raw p a b) : ExtraOrBad (p,a,b) := by
  have H : (rawList.all fun r => decide (ExtraOrBad r))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp H _ (raw_mem p a b R))

private theorem flip_bad (p a b : Nat) (hk : Bad (p,a,b)) : Bad (p,b,a) := by
  obtain ⟨i,I⟩ := hk
  have B : ∀ i : Fin 28, Bad ((inputLabel i).1,(inputLabel i).2.2,(inputLabel i).2.1) := by
    decide +kernel
  simpa only [←I] using B i

private theorem prime_of_bad (p : Nat) (hp : PrimeBad p) : Nat.Prime p := by
  rcases hp with h|h|h <;> rw [h] <;> decide

private theorem residual_or_separates (a b : Kˣ) (H : FieldResidual a b) :
    (∃ k, separates a b k) ∨ ∃ (p : ℕ), PrimeBad p ∧
      ∃ (e : ZMod p→+*K) (x y : ZMod p), e x=(a:K) ∧ e y=(b:K) ∧ Bad (p,x.val,y.val) := by
  obtain ⟨p,x,y,P,X,Y,R⟩ := H
  rcases classify p x y R with ⟨bad,prime,hx,hy⟩ | ⟨k,E⟩
  · right
    letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) (prime_of_bad p prime)).mpr P
    let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
    refine ⟨p,prime,f,(x:ZMod p),(y:ZMod p),by rw [map_natCast,X],by rw [map_natCast,Y],?_⟩
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy]
    exact bad
  · refine Or.inl ⟨(extraCases k).2.2.2,extra_separates a b k ?_ ?_ ?_⟩
    · rw [←congrArg Prod.fst E]
      exact P
    · rw [←congrArg (fun z : Triple => z.2.1) E]
      exact X
    · have h : y=(extraCases k).2.2.1 := congrArg (fun z : Triple => z.2.2) E
      exact Y.trans (congrArg (fun n : Nat => (n:K)) h)

theorem field_adapter (word_cert : FieldWords.{v}) : FieldCover.{u,v} Bad := by
  intro G K _ _ _ _ m x y μ τ two odd co normal
  have pn (g : G) : (μ g)^(Nat.card G)=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_trans (orderOf_map_dvd μ g) (orderOf_dvd_natCard g))
  rcases normal with ⟨nz,x0,y1⟩|⟨_,nz,x1,y0⟩
  · have xN : μ x≠1 := fun z => nz (by simp [z])
    rcases word_cert (μ x) (μ y) (Nat.card G) two odd (pn x) (pn y) xN with ⟨k,S⟩|R
    · exact Or.inl (chart_cycle m _ _ μ τ co x0 y1 k S)
    · rcases residual_or_separates _ _ R with ⟨k,S⟩ | E
      · exact Or.inl (chart_cycle m _ _ μ τ co x0 y1 k S)
      · exact Or.inr E
  · have yN : μ y≠1 := fun z => nz (by simp [z])
    have C : (∃ k : Count, separates (μ y) (μ x) k) ∨ FieldResidual (μ y) (μ x) :=
      word_cert (μ y) (μ x) (Nat.card G) two odd (pn y) (pn x) yN
    have flip : Good y x → Good x y := fun h =>
      h.imp RibbonP3.flip_cycle (fun h => h.imp RibbonP3.flip_cycle (fun h =>
        h.imp RibbonP3.flip_cycle (fun h => h.imp RibbonP3.flip_cycle RibbonP3.flip_cycle)))
    rcases C with ⟨k,S⟩|R
    · exact Or.inl (flip (chart_cycle m _ _ μ τ co y0 x1 k S))
    · rcases residual_or_separates _ _ R with ⟨k,S⟩ | ⟨p,h,f,a,b,A,B,H⟩
      · exact Or.inl (flip (chart_cycle m _ _ μ τ co y0 x1 k S))
      · exact Or.inr ⟨p,h,f,b,a,B,A,flip_bad p a.val b.val H⟩

end RibbonAllOddField
#print axioms RibbonAllOddField.field_adapter
