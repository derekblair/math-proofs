import RibbonD3FiniteRow
import RibbonP11PairUse
import Mathlib.FieldTheory.Finite.Basic

namespace RibbonD3Finite
open Ribbon5Bridge RibbonP11Charts RibbonStationaryChart RibbonD3Field
variable {G : Type*} [Group G]

def invDig (p : Nat) (u : Digits) : Digits :=
  let a := u.1^(p-2)%p
  (a,(p-(u.2*a*a)%p)%p)

def input (p : Nat) (a da b db : Nat) : Params :=
  ⟨p,(a,da),invDig p (a,da),(b,db),invDig p (b,db),a != 1⟩

def jScale {p : Nat} (c : ZMod p) : Jet p →+* Jet p where
  toFun v := ⟨v.fst,c*v.snd⟩
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change c*(u.snd+v.snd)=c*u.snd+c*v.snd
      ring
  map_mul' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change c*(u.fst*v.snd+u.snd*v.fst)=u.fst*(c*v.snd)+(c*u.snd)*v.fst
      ring

def base {p : Nat} : Jet p →+* ZMod p :=
  (TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (ZMod p)).toRingHom

def emb {p : Nat} : ZMod p →+* Jet p := TrivSqZeroExt.inlHom (ZMod p) (ZMod p)

theorem inverse_digits {p : Nat} [Fact p.Prime] (u : (Jet p)ˣ) :
    digits (↑u⁻¹:Jet p)=invDig p (digits (u:Jet p)) := by
  let a := (u:Jet p).fst
  let d := (u:Jet p).snd
  let q := a^(p-2)
  have pn : 2≤p := (Fact.out : p.Prime).two_le
  have one : a*q=1 := by
    have nz : a≠0 := ((u.isUnit.map (base (p:=p))).ne_zero)
    rw [show a*q=a^(p-1) from by unfold q; rw [←pow_succ',show p-2+1=p-1 by omega]]
    exact ZMod.pow_card_sub_one_eq_one nz
  have eq : (↑u⁻¹:Jet p)=⟨q,-(d*q*q)⟩ := by
    apply RibbonP11Pair.inv_unit_of
    apply TrivSqZeroExt.ext
    · exact one
    · change a * -(d*q*q) + d*q=0
      calc
        _ = d*q-(a*q)*(d*q) := by ring
        _ = 0 := by rw [one,one_mul,sub_self]
  rw [eq]
  have e : q.val=a.val^(p-2)%p := by
    unfold q
    rw [←ZMod.natCast_zmod_val a,←Nat.cast_pow,ZMod.val_natCast,
      ZMod.val_natCast,Nat.mod_eq_of_lt a.val_lt]
  apply Prod.ext
  · exact e
  · change (-(d*q*q)).val=(p-(d.val*(a.val^(p-2)%p)*(a.val^(p-2)%p))%p)%p
    simp only [←e,ZMod.neg_val',ZMod.val_mul]
    rw [Nat.mod_mul_mod]

theorem same_key {p : Nat} [Fact p.Prime] (μ : G→*(Jet p)ˣ) (τ : G→Jet p)
    (co : Aff μ τ) (x y : G) (n : RibbonP11.Normalized base x y μ τ)
    (k : Count) (i j : Fin 128)
    (E : run x y ((chart k).start,1) ((chart k).ports.take i.val) =
      run x y ((chart k).start,1) ((chart k).ports.take j.val)) :
    let v := input p (μ x:Jet p).fst.val (μ x:Jet p).snd.val
      (μ y:Jet p).fst.val (μ y:Jet p).snd.val
    (row v k)[i.val]! = (row v k)[j.val]! := by
  dsimp
  have pn : p≠1 := (Fact.out : p.Prime).ne_one
  let xx := (μ x:Jet p).fst
  have pivot : xx.val=1 ↔ xx=1 := by
    refine ⟨?_,fun z => z ▸ ZMod.val_one'' pn⟩
    intro e
    rw [←ZMod.natCast_zmod_val xx,e,Nat.cast_one]
  have st (l : Fin 128) :
      let s := run x y ((chart k).start,1) ((chart k).ports.take l.val)
      let v := input p (μ x:Jet p).fst.val (μ x:Jet p).snd.val
        (μ y:Jet p).fst.val (μ y:Jet p).snd.val
      (row v k)[l.val]! = key p (flatten (s.1,(μ s.2:Jet p),τ s.2)) := by
    dsimp
    rw [row_at]
    have eq := flatFold_sound μ τ co x y ((chart k).ports.take l.val) ((chart k).start,1)
    dsimp only at eq
    rw [eq,fold_sound,map_one,Units.val_one,co.1]
    have u : digits (1:Jet p)=(1,0) := Prod.ext (ZMod.val_one'' pn) ZMod.val_zero
    have z : digits (0:Jet p)=(0,0) := Prod.ext ZMod.val_zero ZMod.val_zero
    rcases n with ⟨ne,x0,y1⟩ | ⟨ex,_,x1,y0⟩
    · have h : (μ x:Jet p).fst.val≠1 := fun e => ne (pivot.mp e)
      simp only [inverse_digits]; simp [Params.next,input,flatten,digits,x0,y1,h,ZMod.val_one'' pn]
    · have h : (μ x:Jet p).fst.val=1 := pivot.mpr ex
      simp only [inverse_digits]; simp [Params.next,input,flatten,digits,x1,y0,h,ZMod.val_one'' pn]
  rw [st,st,E]

end RibbonD3Finite
#print axioms RibbonD3Finite.same_key
