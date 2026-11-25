import IrrMasks
import IrrAnalytic
import Mathlib.Tactic

namespace FibPopularity

theorem mask_ext (n : Nat) (s u : Mask n) (h : ∀ i<n, bit s i=bit u i) : s=u := by
  apply Subtype.ext
  funext i
  simpa [bit_fin] using h i.val i.isLt

def spliceBit {a b : Nat} (s : Mask a) (u : Mask b) (i : Nat) : Bool :=
  if i<a then bit s i else bit u (i-a)

def splice {a b : Nat} (s : Mask a) (u : Mask b) : Mask (a+b) :=
  ⟨fun i => spliceBit s u i.val, by
    constructor
    · intro i hi
      change spliceBit s u i.val = true at hi
      unfold spliceBit at hi
      split at hi
      next h => have h₂ := bit_true_lt s hi; omega
      next h => have h₂ := bit_true_lt u hi; omega
    · intro i j hj hi
      change spliceBit s u i.val = true at hi
      change spliceBit s u j.val = false
      unfold spliceBit at hi ⊢
      split at hi <;> split
      · rw [←hj]
        exact bits_disjoint s hi
      · have hh := bit_true_lt s hi
        omega
      · omega
      · have hh := bits_disjoint u hi
        rwa [show j.val-a=(i.val-a)+1 by omega]⟩

theorem bit_splice {a b : Nat} (s : Mask a) (u : Mask b) (i : Nat) (hi : i<a+b) :
    bit (splice s u) i = spliceBit s u i := by simp [bit,hi,splice]

def cutOK {a b : Nat} (s : Mask (a+b)) : Prop := a=0 ∨ bit s (a-1)=false

theorem splice_cut {a b : Nat} (s : Mask a) (u : Mask b) : cutOK (splice s u) := by
  by_cases ha : a=0
  · exact Or.inl ha
  · right
    rw [bit_splice _ _ _ (by omega)]
    unfold spliceBit
    rw [if_pos (by omega)]
    exact Bool.eq_false_iff.mpr (fun h => by
      have ht := bit_true_lt s h
      omega)

def restrictFirst {a b : Nat} (s : Mask (a+b)) (hs : cutOK s) : Mask a :=
  ⟨fun i => bit s i.val, by
    constructor
    · intro i hi
      change bit s i.val = true at hi
      have hb := i.isLt
      by_cases e : i.val+1=a
      · rcases hs with h|h
        · omega
        · have hE : i.val=a-1 := by omega
          rw [hE,h] at hi
          cases hi
      · omega
    · intro i j e h
      change bit s (i.val) = true at h
      change bit s (j.val) = false
      rw [←e]
      exact bits_disjoint s h⟩

def restrictLast {a b : Nat} (s : Mask (a+b)) : Mask b :=
  ⟨fun i => bit s (a+i.val), by
    constructor
    · intro i h
      have ht := bit_true_lt s h
      omega
    · intro i j e h
      change bit s (a+i.val) = true at h
      change bit s (a+j.val) = false
      rw [show a+j.val=(a+i.val)+1 by omega]
      exact bits_disjoint s h⟩

theorem bit_first {a b : Nat} (s : Mask (a+b)) (h : cutOK s) (i : Nat) (hi : i<a) :
    bit (restrictFirst s h) i = bit s i := by simp [bit,hi,restrictFirst]
theorem bit_last {a b : Nat} (s : Mask (a+b)) (i : Nat) (hi : i<b) :
    bit (restrictLast s) i = bit s (a+i) := by simp [bit,hi,restrictLast]

def cutting (a b : Nat) : {s : Mask (a+b) // cutOK s} ≃ Mask a × Mask b where
  toFun s := (restrictFirst s.val s.property,restrictLast s.val)
  invFun s := ⟨splice s.1 s.2,splice_cut s.1 s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply mask_ext
    intro i hi
    rw [bit_splice _ _ _ hi]
    unfold spliceBit
    split
    next h => exact bit_first s.val s.property _ h
    next h =>
      rw [bit_last _ _ (by omega)]
      congr 1
      omega
  right_inv := by
    intro s
    apply Prod.ext
    · apply mask_ext
      intro i hi
      rw [bit_first _ _ _ hi,bit_splice _ _ _ (by omega)]
      simp [spliceBit,hi]
    · apply mask_ext
      intro i hi
      rw [bit_last _ _ hi,bit_splice _ _ _ (by omega)]
      simp [spliceBit,show ¬a+i<a by omega]

noncomputable instance maskFintype (n : Nat) : Fintype (Mask n) := Fintype.ofFinite _

def mEmpty (n : Nat) : Mask n := ⟨fun _ => false,by simp [Valid]⟩
def mDimer : Mask 2 := ⟨fun i => decide (i.val=0),by unfold Valid; decide⟩

theorem one_mask (u : Mask 1) : u=mEmpty 1 := by
  apply mask_ext
  intro i hi
  have hh : i=0 := by omega
  subst i
  have hfalse : bit u 0 = false := Bool.eq_false_iff.mpr (fun h => by
    have hp := bit_true_lt u h
    omega)
  exact hfalse

theorem dimer_mask (u : Mask 2) (hu : bit u 0=true) : u=mDimer := by
  apply mask_ext
  intro i hi
  have h : i=0 ∨ i=1 := by omega
  rcases h with rfl|rfl
  · exact hu
  · exact bits_disjoint u hu

def notLastDimerEquiv (n : Nat) :
    {s : Mask (n+2) // ¬ bit s n=true} ≃ Mask (n+1) where
  toFun s := restrictFirst (a:=n+1) (b:=1) s.val (Or.inr (by
    have hh := Bool.eq_false_iff.mpr s.property
    rwa [show n+1-1=n by omega]))
  invFun s := ⟨splice (a:=n+1) (b:=1) s (mEmpty 1),by
    have hh := splice_cut s (mEmpty 1)
    rcases hh with h|h
    · omega
    · rw [show n+1-1=n by omega] at h
      simp [h]⟩
  left_inv s := by
    apply Subtype.ext
    have he : cutOK (a:=n+1) (b:=1) s.val := Or.inr (by
      have hh := Bool.eq_false_iff.mpr s.property
      rwa [show n+1-1=n by omega])
    have hh := congrArg Subtype.val ((cutting (n+1) 1).left_inv ⟨s.val,he⟩)
    change splice (a:=n+1) (b:=1) (restrictFirst (a:=n+1) (b:=1) s.val he) (restrictLast (a:=n+1) (b:=1) s.val) = s.val at hh
    rwa [one_mask (restrictLast (a:=n+1) (b:=1) s.val)] at hh
  right_inv s := by
    have hh := congrArg Prod.fst ((cutting (n+1) 1).right_inv (s,mEmpty 1))
    exact hh

lemma lastDimerCut (n : Nat) (s : Mask (n+2)) (hs : bit s n=true) : cutOK (a:=n) (b:=2) s := by
  by_cases hn : n=0
  · exact Or.inl hn
  · right
    exact Bool.eq_false_iff.mpr (fun h => by
      have hh := bits_disjoint s h
      rw [show n-1+1=n by omega,hs] at hh
      cases hh)

def lastDimerEquiv (n : Nat) :
    {s : Mask (n+2) // bit s n=true} ≃ Mask n where
  toFun s := restrictFirst s.val (lastDimerCut n s.val s.property)
  invFun s := ⟨splice s mDimer,by
    rw [bit_splice _ _ _ (by omega)]
    simp [spliceBit]
    rfl⟩
  left_inv s := by
    apply Subtype.ext
    let h := lastDimerCut n s.val s.property
    have hh := congrArg Subtype.val ((cutting n 2).left_inv ⟨s.val,h⟩)
    change splice (restrictFirst s.val h) (restrictLast s.val) = s.val at hh
    have ht : bit (restrictLast (a:=n) (b:=2) s.val) 0=true := by
      rw [bit_last (a:=n) (b:=2) _ _ (by decide)]
      exact s.property
    rwa [dimer_mask _ ht] at hh
  right_inv s := by
    have hh := congrArg Prod.fst ((cutting n 2).right_inv (s,mDimer))
    exact hh

theorem card_mask (n : Nat) : Fintype.card (Mask n) = Nat.fib (n+1) := by
  classical
  induction n using Nat.twoStepInduction with
  | zero =>
    have h : Subsingleton (Mask 0) := ⟨fun s u => mask_ext _ s u (fun i hi => by omega)⟩
    letI : Unique (Mask 0) := { default := mEmpty 0, uniq := fun _ => Subsingleton.elim _ _ }
    simp
  | one =>
    letI : Unique (Mask 1) := { default := mEmpty 1, uniq := one_mask }
    simp
  | more n hn hn1 =>
    have h := Fintype.card_congr (Equiv.sumCompl (fun s : Mask (n+2) => bit s n=true))
    rw [Fintype.card_sum,Fintype.card_congr (lastDimerEquiv n),Fintype.card_congr (notLastDimerEquiv n),hn,hn1] at h
    simpa only [Nat.fib_add_two, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

end FibPopularity
