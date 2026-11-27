import CapProfiles

namespace IU.Eliminate

def pop (a : Nat) : Nat → Nat
  | 0 => 0
  | t+1 => pop (a >>> 1) t + (if a.testBit 0 then 1 else 0)

theorem rank_shift (a b t : Nat) :
    rank a (b+t)=rank a b+rank (a >>> b) t := by
  induction t with
  | zero => simp [rank]
  | succ t ih =>
    rw [Nat.add_succ,rank_succ',rank_succ',ih,Nat.testBit_shiftRight]
    omega

theorem pop_eq (a n : Nat) : pop a n=rank a n := by
  induction n generalizing a with
  | zero => simp [pop,rank]
  | succ n ih =>
    rw [pop,ih]
    have h := rank_shift a 1 n
    rw [show 1+n=n+1 by omega] at h
    rw [h,rank_succ',show rank a 0=0 by simp [rank]]
    omega

def scan (z : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, t, c => decide (z+t≤2*c)
  | s+1,a,t,c =>
    decide (z+t≤2*c) || scan z s (a>>>1) (t+1) (c + (if a.testBit 0 then 1 else 0))

theorem scan_sound (z a t s : Nat) :
    scan z s (a>>>t) t (rank a t)=true ↔
      ∃ j ∈ List.range (s+1), z + (t+j) ≤ 2 * rank a (t+j) := by
  induction s generalizing t with
  | zero => simp [scan]
  | succ s ih =>
    have h : ((a >>> t) >>> 1) = a >>> (t+1) := by rw [Nat.shiftRight_add]
    have c : rank a t + (if (a>>>t).testBit 0 then 1 else 0) = rank a (t+1) := by
      rw [rank_succ',Nat.testBit_shiftRight,Nat.add_zero]
    rw [scan,h,c,Bool.or_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro (H|⟨j,jm,jg⟩)
      · exact ⟨0,List.mem_range.mpr (by omega),by simpa⟩
      · refine ⟨j+1,List.mem_range.mpr (by have := List.mem_range.mp jm; omega),?_⟩
        simpa only [show t+(j+1)=t+1+j by omega] using jg
    · rintro ⟨j,jm,jg⟩
      cases j with
      | zero => exact Or.inl (by simpa using jg)
      | succ j =>
        apply Or.inr
        refine ⟨j,List.mem_range.mpr (by have := List.mem_range.mp jm; omega),?_⟩
        simpa only [show t+j.succ=t+1+j by omega] using jg

def vertexFast (n p q a : Nat) : Bool :=
  let k := pop a n
  decide (p≤k ∧ k≤n-q) && scan (max p (2*k-(n-q))) n a 0 0

theorem vertex_fast (n p q a : Nat) : vertexFast n p q a = vertex n p q a := by
  apply Bool.eq_iff_iff.mpr
  unfold vertexFast vertex
  simp only [pop_eq,Bool.and_eq_true,edge,List.any_eq_true,decide_eq_true_eq]
  have S := scan_sound (max p (2*rank a n-(n-q))) a 0 n
  simp [show rank a 0=0 by simp [rank],Nat.two_mul] at S
  simp [Nat.two_mul,S]

#print axioms vertex_fast
def scanPair (z : Nat) : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, t, c => decide (z+t≤c)
  | s+1,a,b,t,c =>
    decide (z+t≤c) || scanPair z s (a>>>1) (b>>>1) (t+1)
      (c + (if a.testBit 0 then 1 else 0) + (if b.testBit 0 then 1 else 0))

theorem scanPair_sound (z a b t s : Nat) :
    scanPair z s (a>>>t) (b>>>t) t (rank a t+rank b t)=true ↔
      ∃ j ∈ List.range (s+1), z + (t+j) ≤ rank a (t+j) + rank b (t+j) := by
  induction s generalizing t with
  | zero => simp [scanPair]
  | succ s ih =>
    have h (x : Nat) : ((x >>> t) >>> 1) = x >>> (t+1) := by rw [Nat.shiftRight_add]
    have c : rank a t+rank b t + (if (a>>>t).testBit 0 then 1 else 0) +
        (if (b>>>t).testBit 0 then 1 else 0) = rank a (t+1)+rank b (t+1) := by
      rw [rank_succ',rank_succ',Nat.testBit_shiftRight,Nat.testBit_shiftRight,Nat.add_zero]
      omega
    rw [scanPair,h,h,c,Bool.or_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro (H|⟨j,jm,jg⟩)
      · exact ⟨0,List.mem_range.mpr (by omega),by simpa⟩
      · refine ⟨j+1,List.mem_range.mpr (by have := List.mem_range.mp jm; omega),?_⟩
        simpa only [show t+(j+1)=t+1+j by omega] using jg
    · rintro ⟨j,jm,jg⟩
      cases j with
      | zero => exact Or.inl (by simpa using jg)
      | succ j =>
        apply Or.inr
        refine ⟨j,List.mem_range.mpr (by have := List.mem_range.mp jm; omega),?_⟩
        simpa only [show t+j.succ=t+1+j by omega] using jg

def edgeFast (n p q a b : Nat) : Bool :=
  scanPair (max p (pop a n+pop b n-(n-q))) n a b 0 0

theorem edge_fast (n p q a b : Nat) : edgeFast n p q a b=edge n p q a b := by
  apply Bool.eq_iff_iff.mpr
  unfold edgeFast edge
  rw [pop_eq,pop_eq,List.any_eq_true]
  have S := scanPair_sound (max p (rank a n+rank b n-(n-q))) a b 0 n
  simpa [show ∀ x, rank x 0=0 from fun x => by simp [rank]] using S

#print axioms edge_fast
end IU.Eliminate
