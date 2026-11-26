import RibbonAffineBaseData
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic

namespace RibbonAffine
variable {K : Type*} [Field K]

theorem prodP_sound_aux (a b : Kˣ) (fs : List (List Mono)) :
    pl a b (prodP fs)=(fs.map (pl a b)).prod := by
  induction fs with
  | nil => simp [prodP,pl,mon]
  | cons x xs ih => simp [prodP,pl_mul,ih]

theorem mod_poly (t : Kˣ) (p : ℤ) (hp : (p:K)=0)
    (f g h : List Mono) (E : nf f=nf (g++mulP [(0,0,p)] h)) :
    pl t 1 f=pl t 1 g := by
  have H := poly_eq t 1 f _ E
  rw [pl_append,pl_mul] at H
  have z : pl t (1:Kˣ) [(0,0,p)]=0 := by simp [pl,mon,hp]
  rwa [z,zero_mul,add_zero] at H

theorem mod_factor (t : Kˣ) (p c : ℤ) (hp : (p:K)=0) (hc : (c:K)≠0)
    (f : List Mono) (fs : List (List Mono)) (r : List Mono)
    (E : nf f=nf (mulP [(0,0,c)] (prodP fs)++mulP [(0,0,p)] r))
    (root : pl t 1 f=0) :
    ∃ q ∈ fs, pl t 1 q=0 := by
  have H := mod_poly t p hp f _ r E
  rw [root,pl_mul,prodP_sound_aux] at H
  have C : pl t (1:Kˣ) [(0,0,c)]=(c:K) := by simp [pl,mon]
  rw [C] at H
  have Z : (fs.map (pl t 1)).prod=0 := (mul_eq_zero.mp H.symm).resolve_left hc
  obtain ⟨q,m,e⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp Z)
  exact ⟨q,m,e⟩

theorem mod_even_root (t : Kˣ) (n e : Nat) (odd : Odd n) (tn : t^n=1) (two : (2:K)≠0)
    (p : ℤ) (hp : (p:K)=0) (f q r : List Mono)
    (E : nf [(e,0,1),(0,0,1)]=nf (mulP f q++mulP [(0,0,p)] r))
    (H : pl t 1 f=0) : False := by
  have I := mod_poly t p hp _ _ r E
  rw [pl_mul,H,zero_mul] at I
  have J : ((t^(e:ℤ):Kˣ):K)=-1 := by
    simp [pl,mon] at I
    exact eq_neg_of_add_eq_zero_left I
  exact avoid_neg t n odd tn two e J

section Seven
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def U2 : (ZMod 7)ˣ := Units.mk0 2 (by decide)
def U4 : (ZMod 7)ˣ := Units.mk0 4 (by decide)

theorem map_pl {K L : Type*} [Field K] [Field L] (f : K→+*L)
    (a b : Kˣ) (p : List Mono) :
    f (pl a b p)=pl (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) p := by
  induction p with
  | nil => simp [pl]
  | cons x l ih =>
    have M (u : Kˣ) (k : ℤ) : f (↑(u^k):K) =
        (↑((Units.map f.toMonoidHom u)^k):L) := by
      rw [←map_zpow]
      rfl
    simp only [pl_cons,map_add,ih,mon,map_mul,map_intCast,Units.val_mul,M]

theorem map_eRow_inj {K L : Type*} [Field K] [Field L] (f : K→+*L)
    (a b : Kˣ) (r s : Row)
    (E : eRow (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) r =
         eRow (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) s) :
    eRow a b r=eRow a b s := by
  have s' := congrArg (fun p : Bool×Lˣ×L => p.1) E
  have m' := congrArg (fun p : Bool×Lˣ×L => (p.2.1:L)) E
  have v' := congrArg (fun p : Bool×Lˣ×L => p.2.2) E
  have M : f (↑(a^r.i*b^r.j):K)=f (↑(a^s.i*b^s.j):K) := by
    simpa [eRow,map_mul,map_zpow,Units.coe_map] using m'
  have V : f (pl a b r.tr)=f (pl a b s.tr) := by
    rw [map_pl,map_pl]
    exact v'
  apply Prod.ext
  · exact s'
  · exact Prod.ext (Units.ext (f.injective M)) (f.injective V)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem test2 : ∀ i j : Fin 32, i.val<j.val →
    eRow U2 1 (position 6 i.val) ≠ eRow U2 1 (position 6 j.val) := by decide +kernel
private theorem test4 : ∀ i j : Fin 32, i.val<j.val →
    eRow U4 1 (position 6 i.val) ≠ eRow U4 1 (position 6 j.val) := by decide +kernel

theorem seven_separates (t : Kˣ) (p : (7:K)=0) (ht : (t:K)=2 ∨ (t:K)=4)
    (i j : Fin 32) (le : i.val<j.val) :
    eRow t 1 (position 6 i.val) ≠ eRow t 1 (position 6 j.val) := by
  letI : CharP K 7 := (CharP.charP_iff_prime_eq_zero (R:=K) (by decide : Nat.Prime 7)).mpr p
  let f : ZMod 7→+*K := ZMod.castHom (dvd_refl 7) K
  have B : Units.map f.toMonoidHom 1 = 1 := map_one _
  intro e
  rcases ht with g|g
  · have A : Units.map f.toMonoidHom U2 = t := by
      apply Units.ext
      change f (2:ZMod 7) = (t:K)
      rw [show (2:ZMod 7) = ((2:Nat):ZMod 7) from rfl,map_natCast]
      exact g.symm
    apply test2 i j le
    apply map_eRow_inj f
    rwa [A,B]
  · have A : Units.map f.toMonoidHom U4 = t := by
      apply Units.ext
      change f (4:ZMod 7) = (t:K)
      rw [show (4:ZMod 7) = ((4:Nat):ZMod 7) from rfl,map_natCast]
      exact g.symm
    apply test4 i j le
    apply map_eRow_inj f
    rwa [A,B]

end Seven
end RibbonAffine
#print axioms RibbonAffine.seven_separates
