import RibbonStationaryBaseData

namespace RibbonAllOddField
open RibbonStationaryField
open RibbonAffine (Row Mono pl delta delta_zero eRow prodP poly_eq pl_mul subUV
  sub_sound avoid_neg rel_from_mul zpow_drop rel_drop parametric unit_pow_ok nf mulP mon)
variable {K : Type*} [Field K]

def oddFactor : Factor → Prop
  | .bad _ => True
  | .drop _ p _ => p=[(1,0,1),(0,0,1)] ∨ p=[(2,0,1),(1,0,-1),(0,0,1)]
instance (f : Factor) : Decidable (oddFactor f) := by cases f <;> unfold oddFactor <;> infer_instance

def oddCase : PairCase → Prop
  | .slope _ _ _ _ _ _ fs => (fs.all fun f => decide (oddFactor f))=true
  | _ => True
instance (c : PairCase) : Decidable (oddCase c) := by cases c <;> unfold oddCase <;> infer_instance

private theorem odd_array : cases145.all (fun row => row.all (fun c => decide (oddCase c))) = true := by
  decide +kernel

theorem odd_case_valid (i j : Fin 64) : oddCase (chooseCase i j) := by
  unfold chooseCase
  by_cases hi : i.val < cases145.size
  · rw [getElem!_pos cases145 i.val hi]
    have h := Array.all_eq_true.mp odd_array i.val hi
    by_cases hj : j.val < cases145[i.val].size
    · rw [getElem!_pos (cases145[i.val]) j.val hj]
      exact of_decide_eq_true (Array.all_eq_true.mp h j.val hj)
    · rw [getElem!_neg (cases145[i.val]) j.val hj]
      trivial
  · rw [getElem!_neg cases145 i.val hi]
    change oddCase ((#[] : Array PairCase)[j.val]!)
    rw [getElem!_neg (#[] : Array PairCase) j.val (by simp)]
    trivial

theorem reject_drop (t : Kˣ) (n : Nat) (odd : Odd n) (tn : t^n=1) (two : (2:K)≠0)
    (P : Poly) (ok : P=[(1,0,1),(0,0,1)] ∨ P=[(2,0,1),(1,0,-1),(0,0,1)])
    (root : pl t 1 P=0) : False := by
  rcases ok with rfl|rfl
  · apply avoid_neg t n odd tn two 1
    have h : (t:K)+1=0 := by simpa [pl,mon] using root
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left h
  · apply avoid_neg t n odd tn two 3
    have h : (t:K)^2-(t:K)+1=0 := by simpa [pl,mon,sub_eq_add_neg,add_assoc] using root
    rw [Units.val_zpow_eq_zpow_val]
    change (t:K)^((3:Nat):Int) = -1
    rw [zpow_natCast]
    linear_combination ((t:K)+1)*h

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

theorem failure_for_odd (B : Nat → Branch) (k : RibbonStationaryWord.Count) (i j : Fin 64) (c : PairCase) (V : valid B k i j c) (Co : oddCase c)
    (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1) (h : a≠1) (odd : Odd n)
    (two : (2:K)≠0) (hit : eRow a b (RibbonStationaryField.symbol k i.val)=eRow a b (RibbonStationaryField.symbol k j.val)) :
    RibbonStationaryWord.IsMate (RibbonStationaryWord.spec k) i.val j.val ∨ Fault B a b n := by
  let I := RibbonStationaryField.symbol k i.val
  let J := RibbonStationaryField.symbol k j.val
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
    have ho := of_decide_eq_true (List.all_eq_true.mp Co f Ff)
    cases f with
    | drop c U V =>
      exact False.elim (reject_drop t n odd o two U ho T)
    | bad i =>
      exact Or.inr (Or.inr ⟨i,t,by rw [hF.2]; exact E,by rw [hF.1]; exact F,o,tn,T⟩)

end RibbonAllOddField
#print axioms RibbonAllOddField.failure_for_odd
