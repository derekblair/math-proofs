import RibbonAllOddSurfaceData
import RibbonAllOddSlopes
import RibbonStationarySlopeFinalCore

namespace RibbonAllOddField
open RibbonStationaryField
open RibbonAffine (pl mon pl_mul)
variable {K : Type*} [Field K]
theorem drop_surface_char_odd (a : Kˣ) (p d e u n : Nat) (pd : Nat.Prime p)
    (pzero : (p:K)=0) (two : (2:K)≠0) (ae : (2:K)*(a:K)= -1)
    (odd : Odd n) (an : a^n=1) (c : d=e*2^u)
    (H : (p:Int) ∣ (2:Int)^d-(-1:Int)^d)
    (L : ¬ (p:Int) ∣ (2:Int)^e-(-1:Int)^e) : False := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) pd).mpr pzero
  have E : (2:K)^d=(-1:K)^d := by
    apply sub_eq_zero.mp
    have z := (CharP.intCast_eq_zero_iff K p _).mpr H
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_neg,Int.cast_one] using z
  have pq (d : Nat) := congrArg (fun x : K => x^d) ae
  have D : a^d=1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    apply mul_left_cancel₀ (pow_ne_zero d two)
    rw [Units.val_one,mul_one]
    simpa only [mul_pow,←E] using pq d
  have B := odd_drop n odd a an (d:Int) e u (by simpa using c) (by simpa using D)
  have R := pq e
  rw [mul_pow,←Units.val_pow_eq_pow_val,B,Units.val_one,mul_one] at R
  apply L
  apply (CharP.intCast_eq_zero_iff K p _).mp
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_neg,Int.cast_one] using sub_eq_zero.mpr R


private theorem surface_11_b_odd (a b : Kˣ) (P : (11:K)=0) (odd : Odd n) (B : b^n=1)
    (E : pl a b (surfaceBinom 10)=0) :
    (b:K)=1 ∨ (b:K)=3 ∨ (b:K)=4 ∨ (b:K)=5 ∨ (b:K)=9 := by
  have b10 : b^10=1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact sub_eq_zero.mp (by simpa [surface_binom_val] using E)
  have b5 := odd_drop n odd b B 10 5 1 (by decide) (by simpa using b10)
  exact all5_field b P b5

private theorem new_collect (p : Nat) (S : SurfaceSpec) (cost : Array Id) (out : Poly)
    (V : surfaceNewValid p S cost out) (a b : Kˣ) (P : (p:K)=0)
    (r : Fin S.rows.size) (A : pl a b S.rows[r].trans.out=0) (B : pl a b S.rows[r].multiplier.out=0) :
    pl a b out=0 := by
  have E := id_sound_surface _ _ _ _ p (V r).2 a b A B rfl (by simpa using P)
  rwa [(V r).1] at E

private theorem new_surface_join (a b : Kˣ) (n : Nat) (odd : Odd n) (B : b^n=1) (two : (2:K)≠0)
    (p : Nat) (P : (p:K)=0) (u v w : Poly) {I : Id}
    (V : I.rhs=surfGcd ∧ I.valid u v w p)
    (A : pl a b u=0) (G : pl a b v=0) (H : pl a b w=0) : False := by
  have E := id_sound_surface I _ _ _ p V.2 a b A G H (by simpa using P)
  rw [V.1] at E
  have F : (b:K)+1=0 := by simpa [surfGcd,pl,mon] using E
  apply RibbonAffine.avoid_neg b n odd B two 1
  simpa only [zpow_one] using eq_neg_of_add_eq_zero_left F
private theorem all_ordinary (a b : Kˣ) (z : (commonN:K)≠0)
    (A : pl a b surf0.normal=0) (B : pl a b surf1.normal=0) (C : pl a b surf2.normal=0) :
    (b:K)+1=0 := by
  have ⟨d,r,e⟩ := surfJoinOK
  have J := id_sound_surface _ _ _ _ 0 e a b A B C (by simp)
  rw [r,pl_mul] at J
  have Z : (surfN:K) ≠ 0 := by
    obtain ⟨i,E⟩ := d
    intro R
    apply z
    rw [E,Int.cast_mul,R,zero_mul]
  have H : pl a b surfGcd=0 := (mul_eq_zero.mp J).resolve_left (by simpa [natConst,pl,mon] using Z)
  simpa [surfGcd,pl,mon] using H

private theorem primesurface_odd (a b : Kˣ) (H : pl a b sideA0=0) (n : Nat)
    (odd : Odd n) (two : (2:K)≠0) (aN : a^n=1) (a1 : a≠1)
    (C : (commonN:K)=0) : (11:K)=0 ∨ (43:K)=0 ∨ (19:K)=0 ∨ (67:K)=0 := by
  let P : List Nat := [2,2,2,2,2,3,3,3,3,3,5,5,7,7,11,13,17,19,23,43,47,67]
  have E : commonN=(P.prod : Int) := by decide +kernel
  have F : (P.prod:K)=0 := by simpa [E] using C
  rw [Nat.cast_list_prod] at F
  obtain ⟨p,hp,pz⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp F)
  change ((p:Nat):K)=0 at pz
  have ae := surface_eq a b H
  simp only [P,List.mem_cons,List.not_mem_nil,or_false] at hp
  have X : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨
      p=23 ∨ p=43 ∨ p=47 ∨ p=67 := by tauto
  rcases X with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact False.elim (two (by simpa using pz))
  · apply False.elim
    apply a1
    apply Units.ext
    change (a:K)=1
    apply mul_left_cancel₀ two
    rw [ae]
    norm_num at pz ⊢
    linear_combination -pz
  · exact False.elim (drop_surface_char_odd a 5 4 1 2 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char_odd a 7 6 3 1 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact Or.inl (by simpa using pz)
  · exact False.elim (drop_surface_char_odd a 13 12 3 2 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char_odd a 17 8 1 3 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact Or.inr (Or.inr (Or.inl (by simpa using pz)))
  · exact False.elim (drop_surface_char_odd a 23 22 11 1 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact Or.inr (Or.inl (by simpa using pz))
  · exact False.elim (drop_surface_char_odd a 47 46 23 1 n (by decide) pz two ae odd aN (by decide) (by decide) (by decide))
  · exact Or.inr (Or.inr (Or.inr (by simpa using pz)))

private theorem normalized (S : SurfaceSpec) (V : SurfaceGeom S) (a b : Kˣ)
    (sur : pl a b sideA0=0) (notSep : ¬ separates a b S.word) :
    ∃ r : Fin S.rows.size, pl a b S.rows[r].trans.out=0 ∧ pl a b S.rows[r].multiplier.out=0 := by
  classical
  unfold separates at notSep
  push_neg at notSep
  obtain ⟨i,j,l,e,n⟩ := notSep
  exact (cases_surface S a b V i j l sur e).resolve_left n

theorem surface_odd (a b : Kˣ) (n : Nat) (s : pl a b sideA0=0)
    (two : (2:K)≠0) (odd : Odd n)
    (aN : a^n=1) (bN : b^n=1) (a1 : a≠1) :
    (∃ k : RibbonStationaryWord.Count, separates a b k) ∨ SurfaceResidual a b := by
  classical
  by_cases A : separates a b surf0.word
  · exact Or.inl ⟨_,A⟩
  by_cases B : separates a b surf1.word
  · exact Or.inl ⟨_,B⟩
  by_cases C : separates a b surf2.word
  · exact Or.inl ⟨_,C⟩
  obtain ⟨r,Ar,Br⟩ := normalized surf0 surfGeom0 a b s A
  obtain ⟨t,At,Bt⟩ := normalized surf1 surfGeom1 a b s B
  obtain ⟨u,Au,Bu⟩ := normalized surf2 surfGeom2 a b s C
  by_cases neg : (commonN:K)=0
  · rcases primesurface_odd a b s n odd two aN a1 neg with p|p|p|p
    · right
      have T := collect_modular surf0 a b true (fun r => surfMod0 r true) (by simpa using p) r Ar Br
      have ⟨w,Q⟩ := surf11JoinOK
      have E := id_sound_surface _ _ _ _ 11 Q a b T rfl rfl (by simpa using p)
      rw [w] at E
      exact ⟨p,surface_11_a a p two (surface_eq a b s),surface_11_b_odd a b p odd bN E⟩
    · exfalso
      have U := collect_modular surf0 a b false (fun r => surfMod0 r false) (by simpa using p) r Ar Br
      have V := collect_modular surf1 a b false (fun r => surfMod1 r false) (by simpa using p) t At Bt
      have ⟨w,Q⟩ := surf43JoinOK
      have E := id_sound_surface _ _ _ _ 43 Q a b U V rfl (by simpa using p)
      rw [w] at E
      apply surface_43_b b p two odd bN
      simp [surf43target,pl,mon] at E
      linear_combination E
    · exfalso
      exact new_surface_join a b n odd bN two 19 p _ _ _ join19Valid
        (new_collect 19 surf0 _ _ valid19_0 a b p r Ar Br)
        (new_collect 19 surf1 _ _ valid19_1 a b p t At Bt)
        (new_collect 19 surf2 _ _ valid19_2 a b p u Au Bu)
    · exfalso
      exact new_surface_join a b n odd bN two 67 p _ _ _ join67Valid
        (new_collect 67 surf0 _ _ valid67_0 a b p r Ar Br)
        (new_collect 67 surf1 _ _ valid67_1 a b p t At Bt)
        (new_collect 67 surf2 _ _ valid67_2 a b p u Au Bu)
  · exfalso
    have z := all_ordinary a b neg (collect_ordinary surf0 a b _ surfOrd0 neg r Ar Br)
      (collect_ordinary surf1 a b _ surfOrd1 neg t At Bt)
      (collect_ordinary surf2 a b _ surfOrd2 neg u Au Bu)
    apply RibbonAffine.avoid_neg b n odd bN two 1
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left z

end RibbonAllOddField
#print axioms RibbonAllOddField.surface_odd
