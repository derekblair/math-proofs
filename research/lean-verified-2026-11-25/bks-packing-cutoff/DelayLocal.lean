import DelayPattern

namespace CoverCutoff
def posA (i : ℕ) : ℕ := 3*i
def posB (i : ℕ) : ℕ := 3*i+1
def posC (i : ℕ) : ℕ := 3*i+2

def invRank (h r : ℕ) : ℕ :=
  if r<h-1 then posB r
  else if r=h-1 then posA 0
  else if r=h then posB (h-1)
  else if r≤2*h then posA (r-h)
  else posC (r-(2*h+1))

lemma invRank_bound {h r : ℕ} (hh : 2≤h) (hr : r<3*h+1) :
    invRank h r<3*h+1 := by
  unfold invRank
  split_ifs <;> simp only [posA,posB,posC] <;> omega

lemma invRank_spec {h r : ℕ} (hh : 2≤h) (hr : r<3*h+1) :
    familyRank h (invRank h r)=r := by
  unfold invRank
  split_ifs with a b c d
  · rw [posB,familyRank_B,if_neg (by omega)]
  · rw [posA,show 3*(0:ℕ)=0 by decide,familyRank_A0,b]
  · rw [posB,familyRank_B,if_pos rfl,c]
  · rw [posA,familyRank_A (by omega)]
    omega
  · rw [posC,familyRank_C]
    omega

lemma delayed_inv_val {h : ℕ} (hh : 2≤h) (i : Fin (3*h+1)) :
    ((delayed h hh).symm i).val=invRank h i.val := by
  let j : Fin (3*h+1) := ⟨invRank h i.val,invRank_bound hh i.isLt⟩
  have he : delayed h hh j=i := Fin.ext (invRank_spec hh i.isLt)
  have hf := (delayed h hh).symm_apply_eq.mpr he.symm
  exact congrArg Fin.val hf

def Ascending {α : Type} [LT α] (f : ℕ→α) (base len : ℕ) : Prop :=
  ∀ i : ℕ, base ≤ i → i + 1 < base + len → f i < f (i + 1)

def localA {α : Type} (r : ℕ→α) (i : ℕ) := r (posA i)
def localB {α : Type} (r : ℕ→α) (i : ℕ) := r (posB i)
def localC {α : Type} (r : ℕ→α) (i : ℕ) := r (posC i)

def LocalRows {α : Type} [LT α] (r : ℕ→α) (h t : ℕ) : Prop :=
  Ascending (localA r) t (h+1) ∧
  Ascending (localB r) t h ∧
  Ascending (localC r) t h ∧
  localB r (t+h-2) < localA r t ∧
  localA r t < localB r (t+h-1) ∧
  localB r (t+h-1) < localA r (t+1) ∧
  localA r (t+h) < localC r t

lemma asc_lt {α : Type} [Preorder α] {f : ℕ→α} {a n i j : ℕ}
    (h : Ascending f a n) (hi : a ≤ i) (hj : j < a + n) (hij : i < j) : f i<f j := by
  induction j with
  | zero => omega
  | succ j ih =>
     by_cases he : i=j
     · subst i
       exact h j hi hj
     · exact (ih (by omega) (by omega)).trans (h j (by omega) hj)

lemma row_chain_one {α : Type} [Preorder α] {r : ℕ→α} {h t : ℕ}
    (hh : 2≤h) (hr : LocalRows r h t) :
    ∀ q<3*h, r (3*t+invRank h q)<r (3*t+invRank h (q+1)) := by
  intro q hq
  obtain ⟨ha,hb,hc,h1,h2,h3,h4⟩ := hr
  have HP_A (n : ℕ) : 3*t+posA n=posA (t+n) := by simp [posA]; omega
  have HP_B (n : ℕ) : 3*t+posB n=posB (t+n) := by simp [posB]; omega
  have HP_C (n : ℕ) : 3*t+posC n=posC (t+n) := by simp [posC]; omega
  simp only [invRank]
  split_ifs at * <;> simp only [HP_A,HP_B,HP_C] <;>
    first
    | omega
    | (change localA r (t+(q-h)) < localA r (t+((q+1)-h));
       rw [show t+((q+1)-h)=t+(q-h)+1 by omega];
       exact ha _ (by omega) (by omega))
    | (change localB r (t+(q)) < localB r (t+((q+1)));
       rw [show t+((q+1))=t+(q)+1 by omega];
       exact hb _ (by omega) (by omega))
    | (change localC r (t+(q-(2*h+1))) < localC r (t+((q+1)-(2*h+1)));
       rw [show t+((q+1)-(2*h+1))=t+(q-(2*h+1))+1 by omega];
       exact hc _ (by omega) (by omega))
    | (change localB r _ < localA r _; convert h1 using 2 <;> omega)
    | (change localA r _ < localB r _; convert h2 using 2 <;> omega)
    | (change localB r _ < localA r _; convert h3 using 2 <;> omega)
    | (change localA r _ < localC r _; convert h4 using 2 <;> omega)

#print axioms delayed_inv_val
#print axioms row_chain_one
end CoverCutoff
