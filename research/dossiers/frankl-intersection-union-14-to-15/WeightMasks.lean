import VertexFast
import FastColor
namespace IU.Eliminate

def pmask : Nat → Nat → Nat
  | 0, k => if k=0 then 1 else 0
  | n+1, k => pmask n k ||| (if k=0 then 0 else pmask n (k-1) <<< (2^n))

theorem rank_mod_low (a t : Nat) : rank (a%(2^t)) t=rank a t := by
  unfold rank
  congr 1
  apply List.filter_congr
  intro j hj
  rw [Nat.testBit_mod_two_pow]
  simp [List.mem_range.mp hj]

theorem pmask_bit (n k a : Nat) :
    (pmask n k).testBit a = decide (a<2^n ∧ rank a n=k) := by
  induction n generalizing k a with
  | zero =>
    by_cases h : k=0
    · rw [pmask,if_pos h,show (1:Nat)=2^0 by decide,Nat.testBit_two_pow]
      apply Bool.eq_iff_iff.mpr
      simp [rank,h,Nat.lt_one_iff,eq_comm]
    · have g : ¬0=k := Ne.symm h
      simp [pmask,h,rank,g]
  | succ n ih =>
    rw [pmask,Nat.testBit_or,ih]
    have Pow : 2^(n+1)=2^n+2^n := by rw [Nat.pow_succ]; omega
    by_cases L : a<2^n
    · have high : a<2^(n+1) := by rw [Pow]; omega
      have bit := Nat.testBit_lt_two_pow L
      have z : (if k=0 then 0 else pmask n (k-1) <<< (2^n)).testBit a=false := by
        by_cases k0 : k=0 <;> simp [k0,Nat.testBit_shiftLeft,show ¬a≥2^n by omega]
      simp [L,high,rank_succ',bit,z]
    · have le : 2^n≤a := by omega
      by_cases high : a<2^(n+1)
      · have sub : a-2^n < 2^n := by rw [Pow] at high; omega
        have bit := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt le high
        have eq : rank (a-2^n) n = rank a n := by
          rw [←rank_mod_low a n,Nat.mod_eq_sub_mod le,Nat.mod_eq_of_lt sub]
        by_cases k0 : k=0
        · simp [L,high,k0,rank_succ',bit]
        · simp only [L, false_and, decide_false, Bool.false_or, k0, ite_false,
            Nat.testBit_shiftLeft, le, decide_true, Bool.true_and, ih, sub, true_and,
            high, rank_succ', bit, ite_true, eq]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
      · have sub : ¬a-2^n<2^n := by rw [Pow] at high; omega
        by_cases k0 : k=0
        · simp [L,high,k0]
        · simp [L,high,k0,Nat.testBit_shiftLeft,ih,sub]

end IU.Eliminate

namespace IU.Eliminate

theorem rank_mod_le (a b t : Nat) (h : t≤b) : rank (a%(2^b)) t=rank a t := by
  unfold rank
  congr 1
  apply List.filter_congr
  intro j hj
  rw [Nat.testBit_mod_two_pow]
  have jlt := List.mem_range.mp hj
  simp [show j<b by omega]

def anyMask : List Nat → Nat
  | [] => 0
  | m::L => m ||| anyMask L

theorem any_mask (L : List Nat) (a : Nat) :
    (anyMask L).testBit a=true ↔ ∃ m∈L, m.testBit a=true := by
  induction L with
  | nil => simp [anyMask]
  | cons m L ih =>
    simp only [anyMask,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨v,vL,vH⟩)
      · exact ⟨m,Or.inl rfl,h⟩
      · exact ⟨v,Or.inr vL,vH⟩
    · rintro ⟨v,rfl|vL,vH⟩
      · exact Or.inl vH
      · exact Or.inr ⟨v,vL,vH⟩

def liftMask (w m : Nat) : Nat → Nat
  | 0 => m
  | d+1 => let u := liftMask w m d
           u ||| (u <<< (2^(w+d)))

theorem lift_mask_bits {w c m : Nat}
    (core : ∀ a, m.testBit a = decide (a<2^w ∧ c≤rank a w))
    (d a : Nat) :
    (liftMask w m d).testBit a = decide (a < 2^(w+d) ∧ c≤rank a w) := by
  induction d generalizing a with
  | zero => exact core a
  | succ d ih =>
    simp only [liftMask,Nat.testBit_or,Nat.testBit_shiftLeft,ih]
    have Pow : 2^(w+(d+1))=2^(w+d)+2^(w+d) := by rw [←Nat.add_assoc,Nat.pow_succ]; omega
    by_cases L : a<2^(w+d)
    · have H : a<2^(w+(d+1)) := by rw [Pow]; omega
      simp [L,H,show ¬2^(w+d)≤a by omega]
    have le : 2^(w+d)≤a := by omega
    by_cases H : a<2^(w+(d+1))
    · have S : a-2^(w+d)<2^(w+d) := by rw [Pow] at H; omega
      have R : rank (a-2^(w+d)) w = rank a w := by
        rw [←rank_mod_le a (w+d) w (by omega),Nat.mod_eq_sub_mod le,Nat.mod_eq_of_lt S]
      simp [L,le,H,S,R]
    · have S : ¬a-2^(w+d)<2^(w+d) := by rw [Pow] at H; omega
      simp [L,H,S]

def lowerMask (T : Nat → Nat → Nat) (w c : Nat) : Nat :=
  anyMask (((List.range (w+1)).filter (fun j => decide (c≤j))).map (T w))

theorem lower_mask_bits {T : Nat→Nat→Nat} {w c a : Nat}
    (T_ok : ∀ k≤w, T w k = pmask w k) :
    (lowerMask T w c).testBit a = decide (a<2^w ∧ c≤rank a w) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,lowerMask,any_mask]
  constructor
  · rintro ⟨m,hm,hb⟩
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    obtain ⟨kw,kc⟩ := List.mem_filter.mp hk
    have K := List.mem_range.mp kw
    rw [T_ok k (by omega),pmask_bit,decide_eq_true_eq] at hb
    exact ⟨hb.1,hb.2 ▸ of_decide_eq_true kc⟩
  · rintro ⟨A,C⟩
    let k := rank a w
    have K : k≤w := rank_le_length a w
    refine ⟨T w k,List.mem_map.mpr ⟨k,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      decide_eq_true C⟩,rfl⟩,?_⟩
    rw [T_ok k K,pmask_bit]
    exact decide_eq_true ⟨A,rfl⟩

def atLeastPrefix (T : Nat → Nat → Nat) (n w c : Nat) : Nat :=
  liftMask w (lowerMask T w c) (n-w)

theorem prefix_mask_bits {T : Nat→Nat→Nat} {n w c a : Nat}
    (wL : w≤n) (T_ok : ∀ k≤w, T w k = pmask w k) :
    (atLeastPrefix T n w c).testBit a = decide (a<2^n ∧ c≤rank a w) := by
  simpa [atLeastPrefix, Nat.add_sub_of_le wL] using
    (lift_mask_bits (w:=w) (c:=c) (m:=lowerMask T w c) (fun _ => lower_mask_bits T_ok) (n-w) a)

def weightVertexMask (T : Nat → Nat → Nat) (n p q k : Nat) : Nat :=
  T n k &&& anyMask ((List.range (n+1)).map (fun w =>
    atLeastPrefix T n w ((max p (2*k-(n-q)) + w + 1)/2)))

def vertexMask (T : Nat → Nat → Nat) (n p q : Nat) : Nat :=
  anyMask (((List.range (n+1)).filter (fun k => decide (p≤k ∧ k≤n-q))).map
    (weightVertexMask T n p q))

theorem vertex_mask_bit {T : Nat→Nat→Nat} {n p q a : Nat}
    (T_ok : ∀ w≤n, ∀ k≤w, T w k = pmask w k) :
    (vertexMask T n p q).testBit a = decide (a<2^n ∧ vertex n p q a=true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,vertexMask,any_mask]
  constructor
  · rintro ⟨m,hM,hB⟩
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hM
    obtain ⟨kw,kCond⟩ := List.mem_filter.mp hk
    have kn : k≤n := by have := List.mem_range.mp kw; omega
    rw [weightVertexMask,Nat.testBit_and,Bool.and_eq_true,T_ok n le_rfl k kn,pmask_bit,decide_eq_true_eq,any_mask] at hB
    obtain ⟨⟨aN,aK⟩,m,hm,hW⟩ := hB
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have wn : w≤n := by have := List.mem_range.mp hw; omega
    rw [prefix_mask_bits wn (T_ok w wn),decide_eq_true_eq] at hW
    refine ⟨aN, Bool.and_eq_true_iff.mpr ⟨by rwa [aK],?_⟩⟩
    refine List.any_eq_true.mpr ⟨w,hw,?_⟩
    rw [decide_eq_true_eq,aK]
    have sw := hW.2
    rw [Nat.two_mul] at sw
    omega
  · rintro ⟨aN,va⟩
    obtain ⟨sz,e⟩ := Bool.and_eq_true_iff.mp va
    let k := rank a n
    have kn : k≤n := rank_le_length a n
    refine ⟨weightVertexMask T n p q k,List.mem_map.mpr ⟨k,
      List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),sz⟩,rfl⟩,?_⟩
    rw [weightVertexMask,Nat.testBit_and,Bool.and_eq_true,T_ok n le_rfl k kn,pmask_bit,decide_eq_true_eq,any_mask]
    refine ⟨⟨aN,rfl⟩,?_⟩
    obtain ⟨w,hw,ec⟩ := List.any_eq_true.mp e
    have wn : w≤n := by have := List.mem_range.mp hw; omega
    refine ⟨_,List.mem_map.mpr ⟨w,hw,rfl⟩,?_⟩
    rw [prefix_mask_bits wn (T_ok w wn),decide_eq_true_eq]
    refine ⟨aN,?_⟩
    have z := of_decide_eq_true ec
    change max p (k+k-(n-q))+w≤rank a w+rank a w at z
    rw [Nat.two_mul]
    omega

#print axioms vertex_mask_bit
theorem pmask_above {n k : Nat} (lt : n<k) : pmask n k=0 := by
  apply Nat.eq_of_testBit_eq
  intro a
  rw [pmask_bit]
  have H := rank_le_length a n
  simp [show rank a n≠k by omega]

end IU.Eliminate
