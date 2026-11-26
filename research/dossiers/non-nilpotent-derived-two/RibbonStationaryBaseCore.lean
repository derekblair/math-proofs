import RibbonStationaryFieldCore

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (Row Mono pl delta delta_zero eRow prodP poly_eq pl_mul subUV
  sub_sound avoid_neg rel_from_mul zpow_drop rel_drop parametric unit_pow_ok nf mulP mon)
variable {K : Type*} [Field K]

structure Branch where
  u : Int
  v : Int
  p : Poly
  deriving Inhabited

inductive Factor where
  | bad (row : Nat)
  | drop (e : Nat) (p q : Poly)
  deriving Inhabited

def Factor.code (B : Nat → Branch) : Factor → Poly
  | .bad row => (B row).p
  | .drop _ p _ => p

def Factor.valid (B : Nat → Branch) (u v : Int) : Factor → Prop
  | .bad row => (B row).u=u ∧ (B row).v=v
  | .drop e p q => supported e ∧ nf (mulP p q)=nf (binom e)
instance (B : Nat → Branch) (u v : Int) (f : Factor) : Decidable (f.valid B u v) := by
  cases f <;> unfold Factor.valid <;> infer_instance

inductive PairCase where
  | side
  | mate
  | axis (d : Int)
  | same (m : Mono) (fs : List (Fin 4))
  | slope (u v d p q : Int) (m : Mono) (fs : List Factor)
  deriving Inhabited

def allowed (d : Int) := d=1 ∨ d= -1 ∨ d=2 ∨ d= -2
instance (d : Int) : Decidable (allowed d) := by unfold allowed; infer_instance

def valid (B : Nat → Branch) (k : Count) (i j : Fin 64) : PairCase → Prop
  | .side => (symbol k i.val).side≠(symbol k j.val).side
  | .mate => IsMate (spec k) i.val j.val
  | .axis d => (symbol k i.val).i-(symbol k j.val).i=d ∧
      (symbol k i.val).j=(symbol k j.val).j ∧ allowed d
  | .same m fs => unitCoeff m ∧
      nf (delta (symbol k i.val) (symbol k j.val))=nf (mulP [m] (prodP (fs.map simple)))
  | .slope u v d p q m fs => (symbol k i.val).i-(symbol k j.val).i=u*d ∧
      (symbol k i.val).j-(symbol k j.val).j=v*d ∧ allowed d ∧ p*v-q*u=1 ∧ unitCoeff m ∧
      (fs.all fun f => decide (f.valid B u v))=true ∧
      nf (subUV u v (delta (symbol k i.val) (symbol k j.val)))=
        nf (mulP [m] (prodP (fs.map (Factor.code B))))
instance (B : Nat → Branch) (k : Count) (i j : Fin 64) (c : PairCase) :
    Decidable (valid B k i j c) := by cases c <;> unfold valid <;> infer_instance

def Fault (B : Nat → Branch) (a b : Kˣ) (n : Nat) : Prop :=
  pl a b sideA0=0 ∨
    ∃ r : Nat, ∃ t : Kˣ, a=t^(B r).v ∧ b=t^(-(B r).u) ∧ t^n=1 ∧ t≠1 ∧ pl t 1 (B r).p=0

private theorem either_root (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1) (h : a≠1)
    (odd : Odd n) (two : (2:K)≠0) (f : Fin 4) (E : pl a b (simple f)=0) :
    pl a b sideA0=0 := by
  fin_cases f
  · exfalso
    apply h
    apply Units.ext
    simpa [simple,pl,mon,←sub_eq_add_neg,sub_eq_zero] using E
  · exfalso
    apply avoid_neg a n odd ha two 1
    have H : (a:K)+1=0 := by simpa [simple,pl,mon] using E
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left H
  · exfalso
    apply avoid_neg b n odd hb two 1
    have H : (b:K)+1=0 := by simpa [simple,pl,mon] using E
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left H
  · exact E

theorem failure (B : Nat → Branch) (k : Count) (i j : Fin 64) (c : PairCase) (V : valid B k i j c)
    (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1) (h : a≠1) (odd : Odd n) (no3 : ¬3∣n)
    (two : (2:K)≠0) (hit : eRow a b (symbol k i.val)=eRow a b (symbol k j.val)) :
    IsMate (spec k) i.val j.val ∨ Fault B a b n := by
  let I := symbol k i.val
  let J := symbol k j.val
  have z := delta_zero a b I J hit
  have s : I.side=J.side := congrArg Prod.fst hit
  have e : a^I.i*b^I.j = a^J.i*b^J.j := congrArg (fun s : Bool×Kˣ×K => s.2.1) hit
  have r := rel_from_mul a b I.i I.j J.i J.j e
  cases c with
  | side => exact False.elim (V s)
  | mate => exact Or.inl V
  | axis d =>
    rcases (show I.i-J.i=d ∧ I.j=J.j ∧ allowed d from V) with ⟨dx,dy,D⟩
    rw [dx,dy,sub_self,zpow_zero,mul_one] at r
    exact False.elim (h (zpow_drop a n odd ha d D r))
  | same m fs =>
    rcases (show unitCoeff m ∧ nf (delta I J)=nf (mulP [m] (prodP (fs.map simple))) from V) with ⟨U,P⟩
    have W := poly_eq a b _ _ P
    rw [z] at W
    obtain ⟨f,fmem,F⟩ := prod_zero a b m (fs.map simple) W.symm (unitCoeff_sound a b two m U)
    obtain ⟨f,Fmem,rfl⟩ := List.mem_map.mp fmem
    exact Or.inr (Or.inl (either_root a b n ha hb h odd two f F))
  | slope u v d p q m fs =>
    rcases (show I.i-J.i=u*d ∧ I.j-J.j=v*d ∧ allowed d ∧ p*v-q*u=1 ∧ unitCoeff m ∧
        (fs.all fun f => decide (f.valid B u v))=true ∧
        nf (subUV u v (delta I J))=nf (mulP [m] (prodP (fs.map (Factor.code B)))) from V)
        with ⟨dx,dy,D,bez,U,ok,P⟩
    rw [dx,dy] at r
    have r0 := rel_drop a b n ha hb odd u v d D r
    let t := a^p*b^q
    obtain ⟨E,F⟩ := parametric a b u v p q bez r0
    change a=t^v at E
    change b=t^(-u) at F
    have o : t^n=1 := unit_pow_ok a b n ha hb p q
    have tn : t≠1 := by intro e; apply h; rwa [e,one_zpow] at E
    have zz : pl t 1 (subUV u v (delta I J))=0 := by
      rw [←sub_sound,←E,←F]
      exact z
    have W := poly_eq t 1 _ _ P
    rw [zz] at W
    obtain ⟨f,ff,T⟩ := prod_zero t 1 m (fs.map (Factor.code B)) W.symm (unitCoeff_sound t 1 two m U)
    obtain ⟨f,Ff,rfl⟩ := List.mem_map.mp ff
    have hF := of_decide_eq_true (List.all_eq_true.mp ok f Ff)
    cases f with
    | drop c U V =>
      exact False.elim (tn (root_of_binom t n c odd no3 o U V hF.1 hF.2 T))
    | bad i =>
      exact Or.inr (Or.inr ⟨i,t,by rw [hF.2]; exact E,by rw [hF.1]; exact F,o,tn,T⟩)

end RibbonStationaryField
#print axioms RibbonStationaryField.failure
