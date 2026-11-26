import RibbonD3FieldScalar
import RibbonD3FieldCharts

namespace RibbonD3Field
open RibbonAffine (eRow)
variable {K : Type*} [Field K]

def evalList (C : Chart) (a b : Kˣ) : List (Bool × Kˣ × K) :=
  C.reps.toList.map fun r => eRow a b r.toRow

theorem ordered_of_nodup (C : Chart) (a b : Kˣ) (H : (evalList C a b).Nodup) :
    Ordered C a b := by
  intro i j l E
  have iH : i.val < (evalList C a b).length := by simpa [evalList] using i.isLt
  have jH : j.val < (evalList C a b).length := by simpa [evalList] using j.isLt
  have Q : (evalList C a b)[i.val]=(evalList C a b)[j.val] := by
    simpa only [evalList,List.getElem_map,Array.getElem_toList,Fin.getElem_fin] using E
  exact (Nat.ne_of_lt l) (H.getElem_inj_iff.mp Q)

def key (p : Nat) (z : Bool × (ZMod p)ˣ × ZMod p) : Nat :=
  (if z.1 then p*p else 0) + (z.2.1.val.val)*p + z.2.2.val

def keyList (p : Nat) (C : Chart) [Fact (Nat.Prime p)] (a b : (ZMod p)ˣ) : List Nat :=
  (evalList C a b).map (key p)

theorem keys_sound (p : Nat) [Fact (Nat.Prime p)] (C : Chart) (a b : (ZMod p)ˣ)
    (l : List Nat) (H : keyList p C a b = l) (N : l.Nodup) : (evalList C a b).Nodup := by
  unfold keyList at H
  rw [←H] at N
  exact List.Nodup.of_map _ N

theorem direct_ordered (p x y : Nat) [hp : Fact (Nat.Prime p)]
    (hx : (x:ZMod p)≠0) (hy : (y:ZMod p)≠0) (k : Count)
    (D : (evalList (chart k) (Units.mk0 (x:ZMod p) hx) (Units.mk0 (y:ZMod p) hy)).Nodup)
    (a b : Kˣ) (P : (p:K)=0) (X : (a:K)=(x:K)) (Y : (b:K)=(y:K)) :
    Ordered (chart k) a b := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) hp.out).mpr P
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  have A : Units.map f.toMonoidHom (Units.mk0 (x:ZMod p) hx)=a := by
    apply Units.ext
    change f (x:ZMod p)=(a:K)
    rw [map_natCast,X]
  have B : Units.map f.toMonoidHom (Units.mk0 (y:ZMod p) hy)=b := by
    apply Units.ext
    change f (y:ZMod p)=(b:K)
    rw [map_natCast,Y]
  intro i j l E
  apply ordered_of_nodup _ _ _ D i j l
  apply RibbonAffine.map_eRow_inj f
  rwa [A,B]

end RibbonD3Field
#print axioms RibbonD3Field.direct_ordered
