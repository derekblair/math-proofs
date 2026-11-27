import RibbonD3WideArithmetic
import RibbonD3FieldBaseData

namespace RibbonD3Wide
open RibbonD3Field
open RibbonAffine (Row Mono pl mon delta delta_zero eRow nf mulP poly_eq pl_mul prodP
  rel_from_mul zpow_drop rel_drop subUV sub_sound parametric unit_pow_ok avoid_neg)
open RibbonStationaryField (Poly Branch Factor Factor.code Factor.valid prod_zero)
variable {K : Type*} [Field K]

def FactorProfile : Factor→Prop
  | .drop _ f _ => DropProfile f
  | .bad _ => True
instance wideFactorProfileDec (f : Factor) : Decidable (FactorProfile f) := by
  cases f <;> unfold FactorProfile <;> infer_instance

def caseProfile : PairCase→Prop
  | .slope _ _ _ _ _ _ fs => (fs.all fun f => decide (FactorProfile f))=true
  | _ => True
instance wideCaseProfileDec (c : PairCase) : Decidable (caseProfile c) := by
  cases c <;> unfold caseProfile <;> infer_instance

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

theorem base_failure (B : Nat → Branch) (U V : Label) (c : PairCase) (H : pairValid B U V c) (profile : caseProfile c)
    (a b : Kˣ) (n : Nat) (aN : a^n=1) (bN : b^n=1) (a1 : a≠1)
    (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0)
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
      have TT : DropProfile p :=
        of_decide_eq_true (List.all_eq_true.mp profile _ Ff)
      exact False.elim (drop_profile_sound t n odd O two p TT U)
    | bad i =>
      exact Or.inr ⟨i,t,by rw [okF.2]; exact A,by rw [okF.1]; exact Q,O,T,U⟩

def rowCheck (i : Nat) : Bool :=
  (List.range baseChart.reps.size).all fun j =>
    if i<j then decide (pairValid branch baseChart.reps[i]! baseChart.reps[j]! (pick i j) ∧ caseProfile (pick i j)) else true

def chunkCheck (h : Fin 16) : Bool :=
  (List.range 8).all fun i => if 8*h.val+i<baseChart.reps.size then rowCheck (8*h.val+i) else true

set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem checks (h : Fin 16) : chunkCheck h=true := by fin_cases h <;> decide +kernel

private theorem base_valid (i j : Fin baseChart.reps.size) (lt : i.val<j.val) :
    pairValid branch baseChart.reps[i] baseChart.reps[j] (pick i.val j.val) ∧ caseProfile (pick i.val j.val) :=  by
  have hi := i.isLt
  have hj := j.isLt
  have size : baseChart.reps.size≤128 := by decide +kernel
  have H : i.val/8<16 := by omega
  let b : Fin 16 := ⟨i.val/8,H⟩
  have r := checks b
  have e : 8*b.val+i.val%8=i.val := by dsimp [b]; omega
  have m := List.all_eq_true.mp r (i.val%8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have R : rowCheck i.val=true := by simpa only [e,hi,ite_true] using m
  have B := List.all_eq_true.mp R j.val (List.mem_range.mpr hj)
  have S := of_decide_eq_true (by simpa only [lt,ite_true] using B :
    decide (pairValid branch baseChart.reps[i.val]! baseChart.reps[j.val]! (pick i.val j.val) ∧ caseProfile (pick i.val j.val))=true)
  simpa only [Fin.getElem_fin,getElem!_pos baseChart.reps i.val hi,getElem!_pos baseChart.reps j.val hj] using S

theorem base_cases (a b : Kˣ) (n : Nat) (aN : a^n=1) (bN : b^n=1) (a1 : a≠1)
    (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0) :
    Ordered baseChart a b ∨ BaseFault branch a b n := by
  classical
  by_cases S : Ordered baseChart a b
  · exact Or.inl S
  · unfold Ordered at S
    push Not at S
    obtain ⟨i,j,l,eq⟩ := S
    exact Or.inr (base_failure branch _ _ _ (base_valid i j l).1 (base_valid i j l).2 a b n aN bN a1 odd two three eq)

end RibbonD3Wide
#print axioms RibbonD3Wide.base_cases
