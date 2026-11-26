import RibbonD3FieldDirect

namespace RibbonD3Field
variable {K : Type*} [Field K]

abbrev FieldBad (a b : Kˣ) : Prop :=
  ∃ (p : Nat), (p=11 ∨ p=23 ∨ p=29) ∧
    ∃ (f : ZMod p→+*K) (x y : ZMod p),
      f x=(a:K) ∧ f y=(b:K) ∧ (p,x.val,y.val)∈exactBad

abbrev RawFieldBad (a b : Kˣ) : Prop :=
  ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈exactBad

theorem field_bad_flip (a b : Kˣ) (F : FieldBad b a) : FieldBad a b := by
  obtain ⟨p,P,f,x,y,XX,YY,L⟩ := F
  have T : (exactBad.all fun r => decide ((r.1,r.2.2,r.2.1)∈exactBad))=true := by decide +kernel
  exact ⟨p,P,f,y,x,YY,XX,of_decide_eq_true (List.all_eq_true.mp T _ L)⟩

theorem field_bad_embed (a b : Kˣ) (F : RawFieldBad a b) : FieldBad a b := by
  obtain ⟨p,x,y,hp,P,A,B,L⟩ := F
  have T : (exactBad.all fun r => decide ((r.1=11 ∨ r.1=23 ∨ r.1=29) ∧
      r.2.1<r.1 ∧ r.2.2<r.1))=true := by decide +kernel
  obtain ⟨pb,hx,hy⟩ := of_decide_eq_true (List.all_eq_true.mp T _ L)
  obtain ⟨f,u,v,U,V,X,Y⟩ := scalar_digit p hp a b x y P A B hx hy
  exact ⟨p,pb,f,u,v,U,V,by rwa [X,Y]⟩

end RibbonD3Field
