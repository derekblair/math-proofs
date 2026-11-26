import RibbonD3FiniteCertCore
import RibbonD3Orientation

namespace RibbonD3Finite
open RibbonD3Orientation RibbonStationaryChart RibbonD3Stationary
variable {G : Type*} [Group G]

def motion (n : Nat) : Motion := ⟨n/4%2==1,n/2%2==1,n%2==1⟩

def actDig (p : Nat) (m : Motion) (a b : Digits) : Digits × Digits :=
  let A := if m.ix then invDig p a else a
  let B := if m.iy then invDig p b else b
  if m.swap then (B,A) else (A,B)

def scaleDig (p s : Nat) (a : Digits) : Digits := (a.1,s*a.2%p)

def acted (l : Label) (da db n s : Nat) : Label × Nat × Nat :=
  let (A,B) := actDig l.p (motion n) (l.a,da) (l.b,db)
  (⟨l.p,A.1,B.1⟩,(scaleDig l.p s A).2,(scaleDig l.p s B).2)

theorem actDig_sound {p : Nat} [Fact p.Prime] (m : Motion)
    (μ : G→*(Jet p)ˣ) (x y : G) :
    (digits (μ (act m x y).1:Jet p),digits (μ (act m x y).2:Jet p)) =
      actDig p m (digits (μ x:Jet p)) (digits (μ y:Jet p)) := by
  rcases m with ⟨a,b,s⟩
  cases a <;> cases b <;> cases s <;>
    simp [act,motionPow,actDig,map_inv,inverse_digits]

theorem scaleDig_sound {p : Nat} [Fact p.Prime] (s : Nat) (a : Jet p) :
    digits (jScale (s:ZMod p) a) = scaleDig p s (digits a) := by
  apply Prod.ext
  · rfl
  · change ((s:ZMod p)*a.snd).val = s*a.snd.val%p
    rw [ZMod.val_mul,ZMod.val_natCast,Nat.mod_mul_mod]

def paramsLabel {p : Nat} (a b : Jet p) : Label := ⟨p,a.fst.val,b.fst.val⟩

theorem coefficients_after_motion {p : Nat} [Fact p.Prime] (μ : G→*(Jet p)ˣ)
    (x y : G) (l : Label) (da db n s : Nat)
    (lab : paramsLabel (μ x:Jet p) (μ y:Jet p)=l)
    (ha : (μ x:Jet p).snd.val=da) (hb : (μ y:Jet p).snd.val=db) :
    let (X,Y) := act (motion n) x y
    let U := jScale (s:ZMod p) (μ X:Jet p)
    let V := jScale (s:ZMod p) (μ Y:Jet p)
    (paramsLabel U V,U.snd.val,V.snd.val)=acted l da db n s := by
  subst l; subst da; subst db
  have E := actDig_sound (motion n) μ x y
  have A := congrArg Prod.fst E
  have B := congrArg Prod.snd E
  simp only [Prod.fst,Prod.snd] at A B
  simp only [paramsLabel,acted]
  unfold scaleDig
  have q := scaleDig_sound s (μ (act (motion n) x y).1:Jet p)
  have r := scaleDig_sound s (μ (act (motion n) x y).2:Jet p)
  rw [A] at q
  rw [B] at r
  have q2 := congrArg (fun z : Digits => z.2) q
  have r2 := congrArg (fun z : Digits => z.2) r
  apply Prod.ext
  · exact congrArg₂ (Label.mk p) (congrArg (fun z : Digits => z.1) q)
      (congrArg (fun z : Digits => z.1) r)
  · apply Prod.ext
    · exact q2
    · exact r2

theorem scale_norm {p : Nat} (μ : G→*(Jet p)ˣ) (τ : G→Jet p)
    (co : Aff μ τ) (x y : G) (n : RibbonP11.Normalized base x y μ τ) (s : ZMod p) :
    let ν := (Units.map (jScale s).toMonoidHom).comp μ
    let σ := (jScale s) ∘ τ
    Aff ν σ ∧ RibbonP11.Normalized base x y ν σ := by
  dsimp only
  refine ⟨⟨by simp [co.1],fun a b => ?_⟩,?_⟩
  · change jScale s (τ (a*b)) = jScale s (τ a) + jScale s (μ a:Jet p) * jScale s (τ b)
    rw [co.2,map_add,map_mul]
  · rcases n with ⟨hx,tx,ty⟩ | ⟨hx,hy,tx,ty⟩
    · exact Or.inl ⟨hx,by simp [tx],by simp [ty]⟩
    · exact Or.inr ⟨hx,hy,by simp [tx],by simp [ty]⟩

theorem lift_field {p : Nat} (μ : G→*(ZMod p)ˣ) (τ : G→ZMod p)
    (co : Aff μ τ) (x y : G) (n : RibbonP11.Normalized (RingHom.id (ZMod p)) x y μ τ) :
    let ν := (Units.map (emb (p:=p)).toMonoidHom).comp μ
    let σ := emb ∘ τ
    Aff ν σ ∧ RibbonP11.Normalized base x y ν σ := by
  dsimp only
  refine ⟨⟨by simp [co.1],fun a b => ?_⟩,?_⟩
  · change emb (τ (a*b)) = emb (τ a) + emb (μ a:ZMod p) * emb (τ b)
    rw [co.2,map_add,map_mul]
  · rcases n with ⟨hx,tx,ty⟩ | ⟨hx,hy,tx,ty⟩
    · exact Or.inl ⟨hx,by simp [tx],by simp [ty]⟩
    · exact Or.inr ⟨hx,hy,by simp [tx],by simp [ty]⟩

theorem lift_unit {p : Nat} [Fact p.Prime] (r : Jet p) (x : base r≠0) : IsUnit r :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr x)

theorem longUnact (m : Motion) (x y : G) (h : LongGood (act m x y).1 (act m x y).2) :
    LongGood x y := by
  rcases h with a|a|a|a|a|a
  · exact Or.inl (cycle_unact m x y a)
  · exact Or.inr (Or.inl (cycle_unact m x y a))
  · exact Or.inr (Or.inr (Or.inl (cycle_unact m x y a)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (cycle_unact m x y a))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cycle_unact m x y a)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (cycle_unact m x y a)))))

end RibbonD3Finite
#print axioms RibbonD3Finite.coefficients_after_motion
#print axioms RibbonD3Finite.longUnact
