import RibbonStationarySurfaceEndData
import RibbonStationarySurfacePrimes
import RibbonStationaryExtras

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl mon pl_mul)
variable {K : Type*} [Field K]

def SurfaceResidual (a b : Kˣ) : Prop :=
  (11:K)=0 ∧ (a:K)=5 ∧ ((b:K)=1 ∨ (b:K)=3 ∨ (b:K)=4 ∨ (b:K)=5 ∨ (b:K)=9)

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

private theorem primesurface (a b : Kˣ) (H : pl a b sideA0=0) (n : Nat)
    (odd : Odd n) (no3 : ¬3∣n) (two : (2:K)≠0) (aN : a^n=1) (a1 : a≠1)
    (C : (commonN:K)=0) : (11:K)=0 ∨ (43:K)=0 := by
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
  · exact False.elim (drop_surface_char a 5 4 1 2 0 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char a 7 6 1 1 1 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact Or.inl (by simpa using pz)
  · exact False.elim (drop_surface_char a 13 12 1 2 1 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char a 17 8 1 3 0 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char a 19 9 1 0 2 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char a 23 22 11 1 0 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact Or.inr (by simpa using pz)
  · exact False.elim (drop_surface_char a 47 46 23 1 0 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))
  · exact False.elim (drop_surface_char a 67 33 11 0 1 n (by decide) pz two ae odd no3 aN (by decide) (by decide) (by decide))

private theorem normalized (S : SurfaceSpec) (V : SurfaceGeom S) (a b : Kˣ)
    (sur : pl a b sideA0=0) (notSep : ¬ separates a b S.word) :
    ∃ r : Fin S.rows.size, pl a b S.rows[r].trans.out=0 ∧ pl a b S.rows[r].multiplier.out=0 := by
  classical
  unfold separates at notSep
  push_neg at notSep
  obtain ⟨i,j,l,e,n⟩ := notSep
  exact (cases_surface S a b V i j l sur e).resolve_left n

theorem surface_full (a b : Kˣ) (n : Nat) (s : pl a b sideA0=0)
    (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (aN : a^n=1) (bN : b^n=1) (a1 : a≠1) :
    (∃ k : Count, separates a b k) ∨ SurfaceResidual a b := by
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
  · rcases primesurface a b s n odd no3 two aN a1 neg with p|p
    · right
      have T := collect_modular surf0 a b true (fun r => surfMod0 r true) (by simpa using p) r Ar Br
      have ⟨w,Q⟩ := surf11JoinOK
      have E := id_sound_surface _ _ _ _ 11 Q a b T rfl rfl (by simpa using p)
      rw [w] at E
      exact ⟨p,surface_11_a a p two (surface_eq a b s),surface_11_b a b p odd no3 bN E⟩
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
    have z := all_ordinary a b neg (collect_ordinary surf0 a b _ surfOrd0 neg r Ar Br)
      (collect_ordinary surf1 a b _ surfOrd1 neg t At Bt)
      (collect_ordinary surf2 a b _ surfOrd2 neg u Au Bu)
    apply RibbonAffine.avoid_neg b n odd bN two 1
    simpa only [zpow_one] using eq_neg_of_add_eq_zero_left z

end RibbonStationaryField
#print axioms RibbonStationaryField.surface_full
