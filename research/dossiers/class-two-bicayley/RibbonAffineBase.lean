import RibbonAffineBaseData

namespace RibbonAffine
variable {K : Type*} [Field K]
set_option maxRecDepth 16000
set_option maxHeartbeats 0

theorem delta_zero (a b : Kˣ) (u v : Row) (h : eRow a b u=eRow a b v) :
    pl a b (delta u v)=0 := by
  have e := congrArg (fun s : Bool×Kˣ×K => s.2.2) h
  change pl a b u.tr = pl a b v.tr at e
  rw [delta,pl_append,negative_sound,e,add_neg_cancel]

private theorem coeff_ne (two : (2:K)≠0) (m : Mono) (h : scale m) : (m.2.2:K)≠0 := by
  have four : (4:K)≠0 := by
    rw [show (4:K)=2*2 by norm_num]
    exact mul_ne_zero two two
  have F : m.2.2=1 ∨ m.2.2= -1 ∨ m.2.2=2 ∨ m.2.2= -2 ∨ m.2.2=4 ∨ m.2.2= -4 := by
    unfold scale at h
    rcases h with h|h|h <;> omega
  rcases F with e|e|e|e|e|e <;> simp [e,two,four]

private theorem scale_ne (two : (2:K)≠0) (a b : Kˣ) (m : Mono) (h : scale m) :
    pl a b [m]≠0 := by
  have J : pl a b [m] = (m.2.2:K) * (↑(a^m.1*b^m.2.1):K) := by simp [pl,mon]
  rw [J]
  exact mul_ne_zero (coeff_ne two m h) (Units.ne_zero _)

theorem prodP_sound (a b : Kˣ) (fs : List (List Mono)) :
    pl a b (prodP fs) = (fs.map (pl a b)).prod := by
  induction fs with
  | nil => simp [prodP,pl,mon]
  | cons x xs ih => simp [prodP,pl_mul,ih]

private theorem eq_one_val (a : Kˣ) (h : a≠1) : (a:K)≠1 := by
  intro H
  exact h (Units.ext H)

private theorem mono_factor_nonzero (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1)
    (h1 : a≠1) (odd : Odd n) (two : (2:K)≠0) (ext : Bool) : pl a b (acase ext)≠0 := by
  have x1 : (a:K)+ -1≠0 := by rw [←sub_eq_add_neg]; exact sub_ne_zero.mpr (eq_one_val a h1)
  have nn : (a:K)+1≠0 := by
    intro e
    apply avoid_neg a n odd ha two 1
    simpa only [zpow_one] using (eq_neg_of_add_eq_zero_left e)
  have mm : (b:K)+1≠0 := by
    intro e
    apply avoid_neg b n odd hb two 1
    simpa only [zpow_one] using (eq_neg_of_add_eq_zero_left e)
  rw [acase,prodP_sound]
  cases ext <;>
    simp [pl,mon,x1,nn,mm,sub_eq_add_neg]

private theorem factor_context (t : Kˣ) (n : Nat) (h : t^n=1) (odd : Odd n) (two : (2:K)≠0)
    (nt : t≠1) (u v : ℤ) (f : Fac) (F : ck u v f) (z : pl t 1 (code f)=0) :
    ∃ q : Fin 14, (obstruction q).1=u ∧ (obstruction q).2.1=v ∧
      pl t 1 (obstruction q).2.2=0 := by
  cases f with
  | diff =>
    unfold code at z
    have t1 : (t:K)=1 := by
      simp [pl,mon] at z
      exact eq_of_add_neg_eq_zero z
    exact False.elim (nt (Units.ext t1))
  | plus e f q =>
    have M := poly_eq t 1 (mulP f q) [(e,0,1),(0,0,1)] F
    change pl t 1 f=0 at z
    rw [pl_mul,z,zero_mul] at M
    have N : ((t^(e:ℤ):Kˣ):K) = -1 := by
      simp [pl,mon] at M
      exact eq_neg_of_add_eq_zero_left M.symm
    exact False.elim (avoid_neg t n odd h two e N)
  | bad k =>
    exact ⟨k,F.1,F.2,z⟩

/-- A collision in the base word reduces to one of the fixed fourteen
univariate obstructions. All polynomial identities are certificate checked. -/
theorem base_failure (a b : Kˣ) (n : Nat) (ha : a^n=1) (hb : b^n=1)
    (nt : a≠1) (odd : Odd n) (two : (2:K)≠0)
    (i j : Fin 32) (hi : i.val<j.val) (hit : eRow a b (position 0 i.val)=eRow a b (position 0 j.val)) :
    ∃ q : Fin 14, ∃ t : Kˣ,
      a=t^(obstruction q).2.1 ∧ b=t^(-(obstruction q).1) ∧
        t^n=1 ∧ t≠1 ∧ pl t 1 (obstruction q).2.2=0 := by
  let I := position 0 i.val
  let J := position 0 j.val
  have z := delta_zero a b I J hit
  have s : I.side=J.side := congrArg Prod.fst hit
  have e : a^I.i*b^I.j = a^J.i*b^J.j :=
    congrArg (fun s : Bool×Kˣ×K => s.2.1) hit
  have rel := rel_from_mul a b I.i I.j J.i J.j e
  have check : okBase (baseCase i j) I J := checked_base i j hi
  cases id : baseCase i j with
  | side =>
    rw [id] at check
    exact False.elim (check s)
  | axis l =>
    rw [id] at check
    rw [check.1,check.2.1,sub_self,zpow_zero,mul_one] at rel
    exact False.elim (nt (zpow_drop a n odd ha l check.2.2 rel))
  | same ext m =>
    rw [id] at check
    have A := poly_eq a b (delta I J) (mulP [m] (acase ext)) check.2
    rw [z,pl_mul] at A
    exact False.elim (mul_ne_zero (scale_ne two a b m check.1)
      (mono_factor_nonzero a b n ha hb nt odd two ext) A.symm)
  | param u v d p q m fs =>
    rw [id] at check
    obtain ⟨xu,yv,ds,bez,ms,all,symbol⟩ := check
    rw [xu,yv] at rel
    have R := rel_drop a b n ha hb odd u v d ds rel
    let t := a^p*b^q
    have T := parametric a b u v p q bez R
    have P : a=t^v := T.1
    have Q : b=t^(-u) := T.2
    have ord := unit_pow_ok a b n ha hb p q
    have nt' : t≠1 := by
      intro E
      apply nt
      rwa [E,one_zpow] at P
    have z' : pl t 1 (subUV u v (delta I J))=0 := by
      rw [←sub_sound,←P,←Q]
      exact z
    have sh := poly_eq t 1 _ _ symbol
    rw [z',pl_mul,prodP_sound] at sh
    have X : ((fs.map code).map (pl t 1)).prod=0 :=
      (mul_eq_zero.mp sh.symm).resolve_left (scale_ne two t 1 m ms)
    obtain ⟨f,fmem,fr⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp X)
    obtain ⟨g,gmem,gf⟩ := List.mem_map.mp fmem
    have Z : pl t 1 (code g)=0 := gf ▸ fr
    have GC := of_decide_eq_true (List.all_eq_true.mp all g gmem)
    obtain ⟨bidx,bu,bv,br⟩ := factor_context t n ord odd two nt' u v g GC Z
    exact ⟨bidx,t,by rw [bv]; exact P,by rw [bu]; exact Q,ord,nt',br⟩

end RibbonAffine
