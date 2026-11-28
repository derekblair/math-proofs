import AtlasNumeric
import LinkEncoded
import LabelCycle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace BikovEight
open BikovLocal (cyclic)

def packF (f : Nat→Bool) (k : Nat) : Nat :=
  BikovLocal.pack (fun e=>f e.1) ((List.range k).map (fun i=>(i,0)))

theorem packF_small (f : Nat→Bool) (k : Nat) : packF f k<2^k := by
  simpa [packF] using BikovLocal.pack_small (fun (e : Nat×Nat)=>f e.1)
    ((List.range k).map (fun i=>(i,0)))

theorem packF_bit (f : Nat→Bool) (i k : Nat) (hi : i<k) :
    (packF f k).testBit i=f i := by
  apply BikovLocal.pack_bit _ _ _ (i,0)
  simp [List.getElem?_range,hi]

def pick5 (p q r e i j : Nat) : Bool :=
  if j<5 then decide (cyclic 5 i j)
  else if i<5 then (if j=5 then p else if j=6 then q else r).testBit i
  else e.testBit (if j=6 then 0 else if i=5 then 1 else 2)

def pick7 (p i j : Nat) : Bool :=
  if j<7 then decide (cyclic 7 i j) else p.testBit i

private lemma bit_large (p : Nat) (h : p<32)
    (i : Nat) (hi : 5≤i) : p.testBit i=false :=
  Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (n:=2) (by decide) hi))

private lemma bit_large7 (p : Nat) (h : p<128)
    (i : Nat) (hi : 7≤i) : p.testBit i=false :=
  Nat.testBit_lt_two_pow (h.trans_le (Nat.pow_le_pow_right (n:=2) (by decide) hi))

@[local simp] private theorem b613_1 : (613:Nat).testBit 1 = false := by decide
@[local simp] private theorem b613_2 : (613:Nat).testBit 2 = true := by decide
@[local simp] private theorem b613_3 : (613:Nat).testBit 3 = false := by decide
@[local simp] private theorem b613_4 : (613:Nat).testBit 4 = false := by decide
@[local simp] private theorem b613_5 : (613:Nat).testBit 5 = true := by decide
@[local simp] private theorem b613_6 : (613:Nat).testBit 6 = true := by decide
@[local simp] private theorem b613_7 : (613:Nat).testBit 7 = false := by decide
@[local simp] private theorem b613_8 : (613:Nat).testBit 8 = false := by decide
@[local simp] private theorem b613_9 : (613:Nat).testBit 9 = true := by decide
@[local simp] private theorem b613_10 : (613:Nat).testBit 10 = false := by decide
@[local simp] private theorem b613_11 : (613:Nat).testBit 11 = false := by decide
@[local simp] private theorem b613_12 : (613:Nat).testBit 12 = false := by decide
@[local simp] private theorem b613_13 : (613:Nat).testBit 13 = false := by decide
@[local simp] private theorem b613_14 : (613:Nat).testBit 14 = false := by decide
@[local simp] private theorem b613_15 : (613:Nat).testBit 15 = false := by decide
@[local simp] private theorem b613_16 : (613:Nat).testBit 16 = false := by decide
@[local simp] private theorem b613_17 : (613:Nat).testBit 17 = false := by decide
@[local simp] private theorem b613_18 : (613:Nat).testBit 18 = false := by decide
@[local simp] private theorem b613_19 : (613:Nat).testBit 19 = false := by decide
@[local simp] private theorem b613_20 : (613:Nat).testBit 20 = false := by decide
@[local simp] private theorem b613_21 : (613:Nat).testBit 21 = false := by decide
@[local simp] private theorem b613_22 : (613:Nat).testBit 22 = false := by decide
@[local simp] private theorem b613_23 : (613:Nat).testBit 23 = false := by decide
@[local simp] private theorem b613_24 : (613:Nat).testBit 24 = false := by decide
@[local simp] private theorem b613_25 : (613:Nat).testBit 25 = false := by decide
@[local simp] private theorem b613_26 : (613:Nat).testBit 26 = false := by decide
@[local simp] private theorem b613_27 : (613:Nat).testBit 27 = false := by decide
@[local simp] private theorem b1098277_1 : (1098277:Nat).testBit 1 = false := by decide
@[local simp] private theorem b1098277_2 : (1098277:Nat).testBit 2 = true := by decide
@[local simp] private theorem b1098277_3 : (1098277:Nat).testBit 3 = false := by decide
@[local simp] private theorem b1098277_4 : (1098277:Nat).testBit 4 = false := by decide
@[local simp] private theorem b1098277_5 : (1098277:Nat).testBit 5 = true := by decide
@[local simp] private theorem b1098277_6 : (1098277:Nat).testBit 6 = false := by decide
@[local simp] private theorem b1098277_7 : (1098277:Nat).testBit 7 = false := by decide
@[local simp] private theorem b1098277_8 : (1098277:Nat).testBit 8 = false := by decide
@[local simp] private theorem b1098277_9 : (1098277:Nat).testBit 9 = true := by decide
@[local simp] private theorem b1098277_10 : (1098277:Nat).testBit 10 = false := by decide
@[local simp] private theorem b1098277_11 : (1098277:Nat).testBit 11 = false := by decide
@[local simp] private theorem b1098277_12 : (1098277:Nat).testBit 12 = false := by decide
@[local simp] private theorem b1098277_13 : (1098277:Nat).testBit 13 = false := by decide
@[local simp] private theorem b1098277_14 : (1098277:Nat).testBit 14 = true := by decide
@[local simp] private theorem b1098277_15 : (1098277:Nat).testBit 15 = true := by decide
@[local simp] private theorem b1098277_16 : (1098277:Nat).testBit 16 = false := by decide
@[local simp] private theorem b1098277_17 : (1098277:Nat).testBit 17 = false := by decide
@[local simp] private theorem b1098277_18 : (1098277:Nat).testBit 18 = false := by decide
@[local simp] private theorem b1098277_19 : (1098277:Nat).testBit 19 = false := by decide
@[local simp] private theorem b1098277_20 : (1098277:Nat).testBit 20 = true := by decide
@[local simp] private theorem b1098277_21 : (1098277:Nat).testBit 21 = false := by decide
@[local simp] private theorem b1098277_22 : (1098277:Nat).testBit 22 = false := by decide
@[local simp] private theorem b1098277_23 : (1098277:Nat).testBit 23 = false := by decide
@[local simp] private theorem b1098277_24 : (1098277:Nat).testBit 24 = false := by decide
@[local simp] private theorem b1098277_25 : (1098277:Nat).testBit 25 = false := by decide
@[local simp] private theorem b1098277_26 : (1098277:Nat).testBit 26 = false := by decide
@[local simp] private theorem b1098277_27 : (1098277:Nat).testBit 27 = false := by decide
@[local simp] private theorem b6_1 : (6:Nat).testBit 1 = true := by decide
@[local simp] private theorem b6_2 : (6:Nat).testBit 2 = true := by decide
private lemma rem_bit (m i : Nat) (h : 1≤i) : (m%2).testBit i=false :=
  Nat.testBit_lt_two_pow ((Nat.mod_lt _ (by decide)).trans_le
    (Nat.pow_le_pow_right (n:=2) (by decide) h))
theorem bits5 (p q r e : Nat) (hp : p<32) (hq : q<32) (hr : r<32)
    (i j : Fin 8) (ij : i<j) :
    hasEdge (make5 p q r e) i.val j.val=pick5 p q r e i.val j.val := by
  fin_cases i <;> fin_cases j <;> simp_all only [Fin.isValue,Fin.reduceFinMk,Fin.reduceLT]
  all_goals try contradiction
  all_goals norm_num [hasEdge,make5,edgeID,pick5,cyclic,cycle5Mask,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and]
  all_goals simp [bit_large p hp,bit_large q hq,bit_large r hr,rem_bit]

theorem bits7 (p : Nat) (i j : Fin 8) (ij : i<j) :
    hasEdge (make7 p) i.val j.val=pick7 p i.val j.val := by
  fin_cases i <;> fin_cases j <;> simp_all only [Fin.isValue,Fin.reduceFinMk,Fin.reduceLT]
  all_goals try contradiction
  all_goals norm_num [hasEdge,make7,edgeID,pick7,cyclic,cycle7Mask,
    Nat.testBit_or,Nat.testBit_shiftLeft]
  all_goals simp

def independent5 (p : Nat) : Bool :=
  (List.range 5).all (fun i=> !(p.testBit i && p.testBit ((i+1)%5)))

theorem attachment5 (p : Nat) (hp : p<32) (h : independent5 p=true) :
    ∃ i : Fin 11, attach5[i.val]! = p := by
  have t : ∀ i : Fin 32, independent5 i.val=true →
      ∃ j : Fin 11, attach5[j.val]! = i.val := by decide +kernel
  exact t ⟨p,hp⟩ h

theorem word_index (i j k : Fin 11) (e : Nat) (he : e<8) :
    let h := i.val+11*j.val+121*k.val+1331*e
    h<10648 ∧
    word5 h=make5 attach5[i.val]! attach5[j.val]! attach5[k.val]! e ∧
    valid5 h=good5 attach5[i.val]! attach5[j.val]! attach5[k.val]! e := by
  dsimp
  have A : i.val<11 := i.isLt
  have B : j.val<11 := j.isLt
  have C : k.val<11 := k.isLt
  let h := i.val+11*j.val+121*k.val+1331*e
  have a : h%11=i.val := by dsimp [h]; omega
  have b : (h/11)%11=j.val := by dsimp [h]; omega
  have c : (h/121)%11=k.val := by dsimp [h]; omega
  have z : h/1331=e := by dsimp [h]; omega
  change h<10648 ∧ word5 h=make5 attach5[i.val]! attach5[j.val]! attach5[k.val]! e ∧
    valid5 h=good5 attach5[i.val]! attach5[j.val]! attach5[k.val]! e
  exact ⟨by omega,by simp [word5,a,b,c,z],by simp [valid5,a,b,c,z]⟩

#print axioms attachment5
#print axioms bits5
#print axioms bits7
end BikovEight
