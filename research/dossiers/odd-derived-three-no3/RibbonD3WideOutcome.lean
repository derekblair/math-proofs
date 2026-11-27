import RibbonD3WideScalar
import RibbonD3FieldDirectCore

namespace RibbonD3Wide
open RibbonD3Field
variable {K : Type*} [Field K]
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def exactBad : List Triple := [(7,1,2),(7,1,4),(7,2,1),(7,2,2),(7,2,4),(7,4,1),(7,4,2),(7,4,4),(11,1,3),(11,1,4),(11,1,5),(11,1,9),(11,3,1),(11,3,3),(11,3,4),(11,3,5),(11,3,9),(11,4,1),(11,4,3),(11,4,4),(11,4,5),(11,4,9),(11,5,1),(11,5,3),(11,5,4),(11,5,5),(11,5,9),(11,9,1),(11,9,3),(11,9,4),(11,9,5),(11,9,9),(13,1,3),(13,1,9),(13,3,1),(13,3,3),(13,3,9),(13,9,1),(13,9,3),(13,9,9),(19,1,4),(19,1,5),(19,1,7),(19,1,9),(19,1,11),(19,1,17),(19,4,1),(19,4,4),(19,4,5),(19,5,1),(19,5,4),(19,5,5),(19,7,1),(19,7,7),(19,7,11),(19,9,1),(19,9,9),(19,9,17),(19,11,1),(19,11,7),(19,11,11),(19,17,1),(19,17,9),(19,17,17),(23,1,3),(23,1,4),(23,1,6),(23,1,8),(23,1,9),(23,1,13),(23,1,16),(23,1,18),(23,3,1),(23,4,1),(23,6,1),(23,8,1),(23,9,1),(23,9,9),(23,9,18),(23,13,1),(23,16,1),(23,18,1),(23,18,9),(23,18,18),(29,1,7),(29,1,16),(29,1,20),(29,1,25),(29,7,1),(29,16,1),(29,20,1),(29,25,1),(43,1,25),(43,1,31),(43,25,1),(43,31,1)]
def PrimeBad (p : Nat) : Prop := p=7 ∨ p=11 ∨ p=13 ∨ p=19 ∨ p=23 ∨ p=29 ∨ p=43
instance widePrimeBadDecidable (p : Nat) : Decidable (PrimeBad p) := by unfold PrimeBad; infer_instance

abbrev FieldBad (a b : Kˣ) : Prop :=
  ∃ (p : Nat), PrimeBad p ∧
    ∃ (f : ZMod p→+*K) (x y : ZMod p),
      f x=(a:K) ∧ f y=(b:K) ∧ (p,x.val,y.val)∈exactBad

theorem exact_bad_inv (p : Nat) (Q : PrimeBad p) (x y : ZMod p)
    (H : (p,x.val,y.val)∈exactBad) :
    (p,(x⁻¹).val,y.val)∈exactBad ∧ (p,x.val,(y⁻¹).val)∈exactBad := by
  rcases Q with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have C : (exactBad.all fun r => if r.1=7 then decide (
        (7,((r.2.1:ZMod 7)⁻¹).val,r.2.2)∈exactBad ∧
        (7,r.2.1,((r.2.2:ZMod 7)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (7,((x.val:ZMod 7)⁻¹).val,y.val)∈exactBad ∧
        (7,x.val,((y.val:ZMod 7)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=11 then decide (
        (11,((r.2.1:ZMod 11)⁻¹).val,r.2.2)∈exactBad ∧
        (11,r.2.1,((r.2.2:ZMod 11)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (11,((x.val:ZMod 11)⁻¹).val,y.val)∈exactBad ∧
        (11,x.val,((y.val:ZMod 11)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=13 then decide (
        (13,((r.2.1:ZMod 13)⁻¹).val,r.2.2)∈exactBad ∧
        (13,r.2.1,((r.2.2:ZMod 13)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (13,((x.val:ZMod 13)⁻¹).val,y.val)∈exactBad ∧
        (13,x.val,((y.val:ZMod 13)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=19 then decide (
        (19,((r.2.1:ZMod 19)⁻¹).val,r.2.2)∈exactBad ∧
        (19,r.2.1,((r.2.2:ZMod 19)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (19,((x.val:ZMod 19)⁻¹).val,y.val)∈exactBad ∧
        (19,x.val,((y.val:ZMod 19)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=23 then decide (
        (23,((r.2.1:ZMod 23)⁻¹).val,r.2.2)∈exactBad ∧
        (23,r.2.1,((r.2.2:ZMod 23)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (23,((x.val:ZMod 23)⁻¹).val,y.val)∈exactBad ∧
        (23,x.val,((y.val:ZMod 23)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=29 then decide (
        (29,((r.2.1:ZMod 29)⁻¹).val,r.2.2)∈exactBad ∧
        (29,r.2.1,((r.2.2:ZMod 29)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (29,((x.val:ZMod 29)⁻¹).val,y.val)∈exactBad ∧
        (29,x.val,((y.val:ZMod 29)⁻¹).val)∈exactBad)
  · have C : (exactBad.all fun r => if r.1=43 then decide (
        (43,((r.2.1:ZMod 43)⁻¹).val,r.2.2)∈exactBad ∧
        (43,r.2.1,((r.2.2:ZMod 43)⁻¹).val)∈exactBad) else true)=true := by decide +kernel
    have L := List.all_eq_true.mp C _ H
    dsimp only at L
    simpa only [ite_true,ZMod.natCast_zmod_val] using
      (of_decide_eq_true L : (43,((x.val:ZMod 43)⁻¹).val,y.val)∈exactBad ∧
        (43,x.val,((y.val:ZMod 43)⁻¹).val)∈exactBad)

theorem prime_of_bad (p : Nat) (Q : PrimeBad p) : p.Prime := by
  rcases Q with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem field_bad_inv_left (a b : Kˣ) (W : FieldBad a⁻¹ b) : FieldBad a b := by
  obtain ⟨p,P,f,x,y,X,Y,Q⟩ := W
  letI : Fact p.Prime := ⟨prime_of_bad p P⟩
  refine ⟨p,P,f,x⁻¹,y,?_,Y,(exact_bad_inv p P x y Q).1⟩
  rw [map_inv₀,X,Units.val_inv_eq_inv_val,inv_inv]

theorem field_bad_inv_right (a b : Kˣ) (W : FieldBad a b⁻¹) : FieldBad a b := by
  obtain ⟨p,P,f,x,y,X,Y,Q⟩ := W
  letI : Fact p.Prime := ⟨prime_of_bad p P⟩
  refine ⟨p,P,f,x,y⁻¹,X,?_,(exact_bad_inv p P x y Q).2⟩
  rw [map_inv₀,Y,Units.val_inv_eq_inv_val,inv_inv]

theorem scalar_cases (a b : Kˣ) (Q : ScalarPair a b) :
    (∃ k : Count, Ordered (chart k) a b) ∨ FieldBad a b := by
  obtain ⟨p,x,y,hp,P,A,B,L⟩ := Q
  have T : (provisional.all fun r => decide (r∈exactBad ∨ r=(43,23,16)))=true := by decide +kernel
  rcases of_decide_eq_true (List.all_eq_true.mp T _ L) with H|H
  · right
    have T : (exactBad.all fun r => decide (PrimeBad r.1 ∧ r.2.1<r.1 ∧ r.2.2<r.1))=true := by decide +kernel
    obtain ⟨pb,hx,hy⟩ := of_decide_eq_true (List.all_eq_true.mp T _ H)
    obtain ⟨f,u,v,U,V,X,Y⟩ := scalar_digit p hp a b x y P A B hx hy
    exact ⟨p,pb,f,u,v,U,V,by rwa [X,Y]⟩
  · left
    simp only [Prod.mk.injEq] at H
    rcases H with ⟨rfl,rfl,rfl⟩
    letI : Fact (Nat.Prime 43) := ⟨by decide⟩
    exact ⟨3,direct_ordered 43 23 16 (by decide) (by decide) 3
      (keys_sound 43 _ _ _ [43,645,430,2279,3192,2879,1030,600,2449,2940,1091,1349,3198,2285,436,651,49,1898,2544,695,1082,2931,2440,591,1021,2870,3183,1334,1076,689,2538,1892,1343,1085,2934,2443,594,1024,2873,3186,2316,467,682,80,1929,2575,726,1113,1371,3220,2864,1015,585,2434,2925,2962,2428,579,1009,2858,3214,1365,1107,720,2569,1923,74,676,461,2310,3223,2867,1018,588,2437,2928,1079,1337] (by decide +kernel) (by decide +kernel)) a b P A B⟩

end RibbonD3Wide
#print axioms RibbonD3Wide.scalar_cases
#print axioms RibbonD3Wide.field_bad_inv_left
#print axioms RibbonD3Wide.field_bad_inv_right
