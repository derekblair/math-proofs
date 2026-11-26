import RibbonD3FieldChart
import RibbonStationaryBaseCore

namespace RibbonD3Field
open RibbonAffine (Row Mono pl mon delta delta_zero eRow nf mulP poly_eq pl_mul prodP
  rel_from_mul zpow_drop rel_drop subUV sub_sound parametric unit_pow_ok avoid_neg)
open RibbonStationaryField (Poly Branch Factor Factor.code Factor.valid prod_zero root_of_binom)
variable {K : Type*} [Field K]

def surfacePoly (c : Int) : Poly := [(1,1,1),(0,1,1),(1,0,-c)]

inductive Flat where
  | one | negA | negB | surf (c : Int)
  deriving Inhabited

def Flat.poly : Flat → Poly
  | .one => [(1,0,1),(0,0,-1)]
  | .negA => [(1,0,1),(0,0,1)]
  | .negB => [(0,1,1),(0,0,1)]
  | .surf c => surfacePoly c

def surfaceIndex (c : Int) : Prop := c= -3 ∨ c= -2 ∨ c= -1 ∨ c=1 ∨ c=2
instance (c : Int) : Decidable (surfaceIndex c) := by unfold surfaceIndex; infer_instance

def Flat.ok : Flat → Prop
  | .surf c => surfaceIndex c
  | _ => True
instance (f : Flat) : Decidable (f.ok) := by cases f <;> unfold Flat.ok <;> infer_instance

def coeffOK (m : Mono) : Prop := m.2.2.natAbs=1 ∨ m.2.2.natAbs=2 ∨ m.2.2.natAbs=3
instance (m : Mono) : Decidable (coeffOK m) := by unfold coeffOK; infer_instance

theorem coeff_ok_ne (m : Mono) (H : coeffOK m) (a b : Kˣ) (two : (2:K)≠0) (three : (3:K)≠0) :
    pl a b [m]≠0 := by
  have e : pl a b [m] = (m.2.2:K) * (↑(a^m.1*b^m.2.1):K) := by simp [pl,mon]
  rw [e]
  apply mul_ne_zero _ (Units.ne_zero _)
  have X : m.2.2=1 ∨ m.2.2= -1 ∨ m.2.2=2 ∨ m.2.2= -2 ∨ m.2.2=3 ∨ m.2.2= -3 := by
    unfold coeffOK at H
    omega
  rcases X with h|h|h|h|h|h <;> simp [h,two,three]

inductive PairCase where
  | side
  | axis (d : Int)
  | flat (m : Mono) (fs : List Flat)
  | slope (u v d p q : Int) (m : Mono) (fs : List Factor)
  deriving Inhabited

def pairValid (B : Nat → Branch) (U V : Label) : PairCase→Prop
  | .side => U.side≠V.side
  | .axis d => U.i-V.i=d ∧ U.j=V.j ∧ RibbonStationaryField.allowed d
  | .flat m fs => coeffOK m ∧ (fs.all fun f => decide f.ok)=true ∧
      nf (delta U.toRow V.toRow)=nf (mulP [m] (prodP (fs.map Flat.poly)))
  | .slope u v d p q m fs => U.i-V.i=u*d ∧ U.j-V.j=v*d ∧ RibbonStationaryField.allowed d ∧
      p*v-q*u=1 ∧ coeffOK m ∧ (fs.all fun f => decide (f.valid B u v))=true ∧
      nf (subUV u v (delta U.toRow V.toRow))=nf (mulP [m] (prodP (fs.map (Factor.code B))))

instance (B : Nat → Branch) (U V : Label) (c : PairCase) : Decidable (pairValid B U V c) := by
  cases c <;> unfold pairValid <;> infer_instance

def BaseFault (B : Nat → Branch) (a b : Kˣ) (n : Nat) : Prop :=
  (∃ c, surfaceIndex c ∧ pl a b (surfacePoly c)=0) ∨
  (∃ r : Nat, ∃ t : Kˣ, a=t^(B r).v ∧ b=t^(-(B r).u) ∧ t^n=1 ∧ t≠1 ∧ pl t 1 (B r).p=0)

private theorem flat_root (a b : Kˣ) (n : Nat) (aN : a^n=1) (bN : b^n=1) (a1 : a≠1)
    (odd : Odd n) (two : (2:K)≠0) (f : Flat) (F : f.ok) (z : pl a b f.poly=0) :
    ∃ c, surfaceIndex c ∧ pl a b (surfacePoly c)=0 := by
  cases f
  · exfalso
    apply a1
    apply Units.ext
    simpa [Flat.poly,pl,mon,←sub_eq_add_neg,sub_eq_zero] using z
  · exfalso
    apply avoid_neg a n odd aN two 1
    have h : (a:K)+1=0 := by simpa [Flat.poly,pl,mon] using z
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left h
  · exfalso
    apply avoid_neg b n odd bN two 1
    have h : (b:K)+1=0 := by simpa [Flat.poly,pl,mon] using z
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left h
  · exact ⟨_,F,z⟩

theorem base_failure (B : Nat → Branch) (U V : Label) (c : PairCase) (H : pairValid B U V c)
    (a b : Kˣ) (n : Nat) (aN : a^n=1) (bN : b^n=1) (a1 : a≠1)
    (odd : Odd n) (no3 : ¬3∣n) (two : (2:K)≠0) (three : (3:K)≠0)
    (eq : eRow a b U.toRow=eRow a b V.toRow) : BaseFault B a b n := by
  have z := delta_zero a b U.toRow V.toRow eq
  have s : U.side=V.side := congrArg Prod.fst eq
  have m : a^U.i*b^U.j=a^V.i*b^V.j := congrArg (fun p : Bool×Kˣ×K => p.2.1) eq
  have r := rel_from_mul a b U.i U.j V.i V.j m
  cases c with
  | side => exact False.elim (H s)
  | axis d =>
    obtain ⟨dx,dy,D⟩ := H
    rw [dx,dy,sub_self,zpow_zero,mul_one] at r
    exact False.elim (a1 (zpow_drop a n odd aN d D r))
  | flat m fs =>
    obtain ⟨h,ok,P⟩ := H
    have W := poly_eq a b _ _ P
    rw [z] at W
    obtain ⟨f,fmem,F⟩ := prod_zero a b m (fs.map Flat.poly) W.symm (coeff_ok_ne m h a b two three)
    obtain ⟨f,Fmem,rfl⟩ := List.mem_map.mp fmem
    exact Or.inl (flat_root a b n aN bN a1 odd two f (of_decide_eq_true (List.all_eq_true.mp ok f Fmem)) F)
  | slope u v d p q m fs =>
    obtain ⟨dx,dy,D,bez,M,ok,P⟩ := H
    rw [dx,dy] at r
    have r0 := rel_drop a b n aN bN odd u v d D r
    let t := a^p*b^q
    obtain ⟨A,Q⟩ := parametric a b u v p q bez r0
    change a=t^v at A
    change b=t^(-u) at Q
    have O : t^n=1 := unit_pow_ok a b n aN bN p q
    have T : t≠1 := by intro h; apply a1; rwa [h,one_zpow] at A
    have Z : pl t 1 (subUV u v (delta U.toRow V.toRow))=0 := by
      rw [←sub_sound,←A,←Q]
      exact z
    have W := poly_eq t 1 _ _ P
    rw [Z] at W
    obtain ⟨f,ff,U⟩ := prod_zero t 1 m (fs.map (Factor.code B)) W.symm (coeff_ok_ne m M t 1 two three)
    obtain ⟨f,Ff,rfl⟩ := List.mem_map.mp ff
    have okF := of_decide_eq_true (List.all_eq_true.mp ok f Ff)
    cases f with
    | drop e p q =>
      exact False.elim (T (root_of_binom t n e odd no3 O p q okF.1 okF.2 U))
    | bad i =>
      exact Or.inr ⟨i,t,by rw [okF.2]; exact A,by rw [okF.1]; exact Q,O,T,U⟩

end RibbonD3Field
#print axioms RibbonD3Field.base_failure
