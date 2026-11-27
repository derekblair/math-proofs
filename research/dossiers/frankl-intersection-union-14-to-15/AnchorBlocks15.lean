import VertexFast
import ProductWitness
import Mathlib.Data.Finset.Prod

namespace IU.IU15Anchor
open IU.Eliminate

def lows : Finset Nat := (List.range 64 |>.filter fun a => decide (4≤rank a 6)).toFinset
def highs : Finset Nat := (List.range 256 |>.filter fun a => decide (rank a 8≤3)).toFinset
def maps (P : Nat × Nat × Nat) : Nat := P.1 + 64 * P.2.1 + 128 * P.2.2
def anchorFamily : Finset Nat := (lows ×ˢ (Finset.range 2 ×ˢ highs)).image maps

theorem lower_size : lows.card=22 := by decide +kernel
theorem upper_size : highs.card=93 := by decide +kernel

theorem rank_mod (a t : Nat) : rank (a%(2^t)) t=rank a t := by
  unfold rank
  congr 1
  apply List.filter_congr
  intro j hj
  rw [Nat.testBit_mod_two_pow]
  simp [List.mem_range.mp hj]

theorem rank_high (a : Nat) : rank a 15-rank a 7=rank (a/128) 8 := by
  have h := rank_shift a 7 8
  change rank a 15=rank a 7+rank (a>>>7) 8 at h
  rw [Nat.shiftRight_eq_div_pow,show 2^7=128 by decide] at h
  omega

theorem into_anchor {a : Nat} (h : a<32768)
    (l : 4 ≤ rank a 6) (r : rank a 15-rank a 7 ≤ 3) :
    a∈anchorFamily := by
  have a6 := rank_mod a 6
  rw [show 2^6=64 by decide] at a6
  have ai := rank_high a
  let X := (a%64,(a/64)%2,a/128)
  have hX : X∈lows ×ˢ (Finset.range 2 ×ˢ highs) := by
    simp only [X,Finset.mem_product,lows,highs,List.mem_toFinset,List.mem_filter,List.mem_range,
      Finset.mem_range,decide_eq_true_eq]
    constructor
    · exact ⟨Nat.mod_lt _ (by decide),a6 ▸ l⟩
    · exact ⟨Nat.mod_lt _ (by decide),by omega,ai ▸ r⟩
  apply Finset.mem_image.mpr
  exact ⟨X,hX,by unfold X maps; dsimp; omega⟩

theorem anchor_size : anchorFamily.card=4092 := by
  classical
  have inj : Set.InjOn maps (↑(lows ×ˢ (Finset.range 2 ×ˢ highs)) : Set (Nat × Nat × Nat)) := by
    rintro ⟨a,b,c⟩ hm ⟨x,y,z⟩ hn Eq
    have A := (Finset.mem_product.mp hm).1
    have X := (Finset.mem_product.mp hn).1
    have B := (Finset.mem_product.mp (Finset.mem_product.mp hm).2).1
    have Y := (Finset.mem_product.mp (Finset.mem_product.mp hn).2).1
    simp only [lows,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq] at A X
    rw [Finset.mem_range] at B Y
    change b<2 at B
    change y<2 at Y
    change a+64*b+128*c=x+64*y+128*z at Eq
    have eax : a=x := by omega
    have eby : b=y := by omega
    have ecz : c=z := by omega
    simp [eax,eby,ecz]

  unfold anchorFamily
  rw [Finset.card_image_of_injOn inj,Finset.card_product,Finset.card_product,
      Finset.card_range,lower_size,upper_size]
  
theorem anchor_product : (productMasks 15 6 8 2 2).toFinset=anchorFamily := by
  ext a
  constructor
  · intro h
    obtain ⟨ha,g⟩ := List.mem_filter.mp (List.mem_toFinset.mp h)
    have cond := of_decide_eq_true g
    change 8≤2*rank a 6 ∧ 2*(rank a 15-rank a 7)≤6 at cond
    exact into_anchor (List.mem_range.mp ha) (by omega) (by omega)
  · intro h
    obtain ⟨⟨x,y,z⟩,M,rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_product,lows,highs,List.mem_toFinset,List.mem_filter,List.mem_range,
      Finset.mem_range,decide_eq_true_eq] at M
    let a := maps (x,y,z)
    have eq : a=x+64*y+128*z := rfl
    have hi : a/128=z := by omega
    have lo : a%64=x := by omega
    have l := rank_mod a 6
    have r := rank_high a
    rw [show 2^6=64 by decide,lo] at l
    rw [hi] at r
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega),?_⟩
    change decide (8≤2*rank a 6 ∧ 2*(rank a 15-rank a 7)≤6)=true
    exact decide_eq_true (by omega)

theorem product_len15 : (productMasks 15 6 8 2 2).length=4092 := by
  rw [←anchor_size,←anchor_product,List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ List.nodup_range

#print axioms product_len15
def maps14 (P : Nat × Nat) : Nat := P.1 + 64*P.2
def anchorFamily14 : Finset Nat := (lows ×ˢ highs).image maps14

theorem anchor_size14 : anchorFamily14.card=2046 := by
  have inj : Set.InjOn maps14 (↑(lows ×ˢ highs) : Set (Nat × Nat)) := by
    rintro ⟨a,b⟩ hm ⟨c,d⟩ hn E
    have A := (Finset.mem_product.mp hm).1
    have C := (Finset.mem_product.mp hn).1
    simp only [lows,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq] at A C
    change a+64*b=c+64*d at E
    have e : a=c := by omega
    have f : b=d := by omega
    simp [e,f]
  unfold anchorFamily14
  rw [Finset.card_image_of_injOn inj,Finset.card_product,lower_size,upper_size]

theorem rank_high14 (a : Nat) : rank a 14-rank a 6=rank (a/64) 8 := by
  have h := rank_shift a 6 8
  change rank a 14=rank a 6+rank (a>>>6) 8 at h
  rw [Nat.shiftRight_eq_div_pow,show 2^6=64 by decide] at h
  omega

theorem anchor_product14 : (productMasks 14 6 8 2 2).toFinset=anchorFamily14 := by
  ext a
  have lm : rank (a%64) 6=rank a 6 := rank_mod a 6
  have hm := rank_high14 a
  constructor
  · intro h
    obtain ⟨ha,g⟩ := List.mem_filter.mp (List.mem_toFinset.mp h)
    have cond := of_decide_eq_true g
    change 8≤2*rank a 6 ∧ 2*(rank a 14-rank a 6)≤6 at cond
    have b : a<16384 := List.mem_range.mp ha
    apply Finset.mem_image.mpr
    refine ⟨(a%64,a/64),?_,?_⟩
    · simp only [lows,highs,Finset.mem_product,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq]
      exact ⟨⟨Nat.mod_lt _ (by decide),by omega⟩, by omega, by omega⟩
    · unfold maps14
      dsimp
      omega
  · intro h
    obtain ⟨⟨x,z⟩,M,E⟩ := Finset.mem_image.mp h
    change x+64*z=a at E
    simp only [lows,highs,Finset.mem_product,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq] at M
    have low : a%64=x := by omega
    have high : a/64=z := by omega
    rw [low] at lm
    rw [high] at hm
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega),?_⟩
    change decide (8≤2*rank a 6 ∧ 2*(rank a 14-rank a 6)≤6)=true
    exact decide_eq_true (by omega)

theorem product_len14 : (productMasks 14 6 8 2 2).length=2046 := by
  rw [←anchor_size14,←anchor_product14,List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ List.nodup_range

#print axioms product_len14
end IU.IU15Anchor
