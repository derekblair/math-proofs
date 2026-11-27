import EliminateDom

namespace IU.Eliminate

inductive PaintTree
  | leaf (cls : List Nat)
  | fork (split : Nat) (left right : PaintTree)

def PaintTree.lookup : PaintTree → Nat → List Nat
  | .leaf c, _ => c
  | .fork s l r, i => if i<s then l.lookup i else r.lookup (i-s)

def PaintTree.valid : PaintTree → Nat → Prop
  | .leaf _, k => k=1
  | .fork s l r, k => s≤k ∧ l.valid s ∧ r.valid (k-s)

def PaintTree.good (n p q : Nat) : PaintTree → Prop
  | .leaf c => c.Pairwise (fun a b => edge n p q a b = false)
  | .fork _ l r => l.good n p q ∧ r.good n p q

def PaintTree.mask : PaintTree → Nat
  | .leaf c => packed c
  | .fork _ l r => l.mask ||| r.mask

def PaintTree.goodDec (n p q : Nat) : (t : PaintTree) → Decidable (t.good n p q)
  | .leaf c => by unfold PaintTree.good; infer_instance
  | .fork s l r => by
    unfold PaintTree.good
    letI := l.goodDec n p q
    letI := r.goodDec n p q
    infer_instance

instance (t : PaintTree) (n p q : Nat) : Decidable (t.good n p q) := t.goodDec n p q

def PaintTree.validDec : (t : PaintTree) → (k : Nat) → Decidable (t.valid k)
  | .leaf c, k => by unfold PaintTree.valid; infer_instance
  | .fork s l r, k => by
    unfold PaintTree.valid
    letI := l.validDec s
    letI := r.validDec (k-s)
    infer_instance

instance (t : PaintTree) (k : Nat) : Decidable (t.valid k) := t.validDec k

theorem PaintTree.at_good {n p q : Nat} (t : PaintTree) (ok : t.good n p q) (i : Nat) :
    (t.lookup i).Pairwise (fun a b => edge n p q a b = false) := by
  induction t generalizing i with
  | leaf c => exact ok
  | fork s l r il ir =>
    change l.good n p q ∧ r.good n p q at ok
    unfold lookup
    split
    · exact il ok.1 i
    · exact ir ok.2 (i-s)

theorem PaintTree.mask_cover (t : PaintTree) {k a : Nat}
    (wf : t.valid k) (bit : t.mask.testBit a=true) :
    ∃ i<k, a∈t.lookup i := by
  induction t generalizing k with
  | leaf c =>
    change k=1 at wf
    subst k
    exact ⟨0,by decide,(packed_mem c a).mp bit⟩
  | fork s l r il ir =>
    obtain ⟨hk,wl,wr⟩ := wf
    change (l.mask ||| r.mask).testBit a=true at bit
    rw [Nat.testBit_or,Bool.or_eq_true] at bit
    rcases bit with bl|br
    · obtain ⟨i,hi,ha⟩ := il wl bl
      exact ⟨i,by omega,by simpa [PaintTree.lookup,hi]⟩
    · obtain ⟨i,hi,ha⟩ := ir wr br
      exact ⟨s+i,by omega,by simpa [PaintTree.lookup,show ¬s+i<s by omega]⟩

end IU.Eliminate
