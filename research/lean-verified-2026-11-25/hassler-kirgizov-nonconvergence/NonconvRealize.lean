import NonconvCounts
import Statement

namespace Nonconv
set_option maxRecDepth 16384
open Emerging

set_option maxHeartbeats 16000000 in
theorem overlapCompare : ∀ u v : State, edge u v=true →
    ∀ a b : Fin 8, (word u (a.val+1) > word u (b.val+1)) ↔ word v a.val > word v b.val := by decide

theorem distinct_words : ∀ u v : State,
    (∀ a b : Fin 9, word u a.val > word u b.val ↔ word v a.val > word v b.val) → u=v := by
  decide

theorem valid_word : ∀ (u : State) (i : Fin 9), 0 < word u i.val ∧ word u i.val ≤ 9 := by decide
theorem injective_word : ∀ (u : State) (i j : Fin 9), word u i.val = word u j.val → i=j := by decide

theorem rank_exists {n : Nat} (g : Fin n → Nat) (hg : Function.Injective g) :
    ∃ f : Perm n, ∀ a b, f a < f b ↔ g a < g b := by
  classical
  let vals := Finset.univ.image g
  have hc : vals.card=n := by simp [vals,Finset.card_image_of_injective _ hg]
  let e : Fin n ≃ vals := Equiv.ofBijective
    (fun j => ⟨g j, Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun a b h => hg (congrArg Subtype.val h),fun b => by
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp b.property
      exact ⟨a,Subtype.ext ha⟩⟩
  let ord := vals.orderIsoOfFin hc
  exact ⟨e.trans ord.symm.toEquiv, fun a b => ord.symm.lt_iff_lt⟩

/-- Coherent overlap word assignment over all starts 0..m (m adjacent steps). -/
def WalkValid (m : Nat) (u : Fin (m+1) → State) : Prop :=
  ∀ i : Fin m, edge (u i.castSucc) (u i.succ) = true

def tagExt {m : Nat} (u : Fin (m+1) → State) (i : Nat) : State :=
  if h : i<m+1 then u ⟨i,h⟩ else 0

theorem edge_ext {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u)
    {i : Nat} (hi : i<m) : edge (tagExt u i) (tagExt u (i+1))=true := by
  have he := h ⟨i,hi⟩
  simpa [tagExt,show i<m+1 by omega,show i+1<m+1 by omega] using he

theorem pathPhase {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u)
    (i : Nat) (hi : i<m+1) :
    (row (tagExt u i)).lane = (row (tagExt u 0)).lane ∧
      (row (tagExt u i)).phase = ((row (tagExt u 0)).phase+i)%3 := by
  induction i with
  | zero =>
    have ho := (labelBounds (tagExt u 0)).2
    simp [Nat.mod_eq_of_lt ho]
  | succ i ih =>
    have hE := edge_ext u h (by omega : i<m)
    have he := overlapTags (tagExt u i) (tagExt u (i+1)) (of_decide_eq_true hE)
    have hs := ih (by omega)
    constructor
    · omega
    · rw [hs.2] at he
      omega

theorem transportCompare {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u)
    (b a j k : Nat) (hj₁ : a≤j) (hk₁ : a≤k) (hj₂ : b≤j) (hk₂ : b≤k)
    (hj₃ : j<a+9) (hk₃ : k<a+9) (hb : b≤m) (hab : a≤b) :
    word (tagExt u a) (j-a) > word (tagExt u a) (k-a) ↔
      word (tagExt u b) (j-b) > word (tagExt u b) (k-b) := by
  induction b with
  | zero =>
    have e : a=0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases ha : a=b+1
    · subst a
      rfl
    · have hh := ih (by omega) (by omega) (by omega) (by omega)
      let r : Fin 8 := ⟨j-(b+1),by omega⟩
      let s : Fin 8 := ⟨k-(b+1),by omega⟩
      have he := overlapCompare (tagExt u b) (tagExt u (b+1)) (edge_ext u h (by omega)) r s
      have er : r.val+1=j-b := by dsimp [r]; omega
      have es : s.val+1=k-b := by dsimp [s]; omega
      rw [er,es] at he
      exact hh.trans he

def anchor (m o i : Nat) : Nat := min (3*block o i-o) m
def anchorWord {m : Nat} (u : Fin (m+1) → State) (i : Nat) : Nat :=
  let a := anchor m (row (tagExt u 0)).phase i
  word (tagExt u a) (i-a)

lemma anchor_range (m o i : Nat) (hi : i < m+9) :
    anchor m o i ≤ m ∧ anchor m o i ≤ i ∧ i < anchor m o i+9 := by
  unfold anchor block
  simp only [Nat.min_def]
  split <;> omega

lemma anchor_eq (m o i j : Nat) (h : block o i=block o j) :
    anchor m o i = anchor m o j := by simp [anchor,h]

lemma anchor_word_range {m : Nat} (u : Fin (m+1) → State) (i : Nat) (hi : i<m+9) :
    0 < anchorWord u i ∧ anchorWord u i ≤ 9 := by
  let a := anchor m (row (tagExt u 0)).phase i
  have hh := anchor_range m (row (tagExt u 0)).phase i hi
  exact valid_word (tagExt u a) ⟨i-a,by dsimp [a]; omega⟩

def scoreKey {m : Nat} (u : Fin (m+1) → State) (i : Nat) : Nat :=
  let g := block (row (tagExt u 0)).phase i
  let d := if (row (tagExt u 0)).lane=0 then g else m+9-g
  10*d+anchorWord u i

lemma transport_unordered {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u)
    (a b j k : Nat) (ha : a≤m) (hb : b≤m)
    (hA : a≤j ∧ a≤k ∧ j<a+9 ∧ k<a+9)
    (hB : b≤j ∧ b≤k ∧ j<b+9 ∧ k<b+9) :
    word (tagExt u a) (j-a) > word (tagExt u a) (k-a) ↔
      word (tagExt u b) (j-b) > word (tagExt u b) (k-b) := by
  by_cases hl : a≤b
  · exact transportCompare u h b a j k hA.1 hA.2.1 hB.1 hB.2.1 hA.2.2.1 hA.2.2.2 hb hl
  · exact (transportCompare u h a b j k hB.1 hB.2.1 hA.1 hA.2.1 hB.2.2.1 hB.2.2.2 ha (by omega)).symm

theorem scoreMatches {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u)
    (l : Nat) (hl : l ≤ m) : Matches (scoreKey u) l (tagExt u l) := by
  intro a ha b hb
  let o := (row (tagExt u 0)).phase
  have hp := pathPhase u h l (by omega)
  have hbA : block o (l+a) = (o+l)/3+block (row (tagExt u l)).phase a := by
    rw [hp.2]
    unfold block
    dsimp [o]
    omega
  have hbB : block o (l+b) = (o+l)/3+block (row (tagExt u l)).phase b := by
    rw [hp.2]
    unfold block
    dsimp [o]
    omega
  have nla : block o (l+a) ≤ m+9 := by unfold block; have := (labelBounds (tagExt u 0)).2; dsimp [o]; omega
  have nlb : block o (l+b) ≤ m+9 := by unfold block; have := (labelBounds (tagExt u 0)).2; dsimp [o]; omega
  have hA := anchor_word_range u (l+a) (by omega)
  have hB := anchor_word_range u (l+b) (by omega)
  rcases Nat.lt_trichotomy (block o (l+a)) (block o (l+b)) with lt|eq|gt
  · have hoo := rowCross (tagExt u l) ⟨a,ha⟩ ⟨b,hb⟩ (by dsimp; omega)
    rw [hp.1] at hoo
    by_cases he : (row (tagExt u 0)).lane=0
    · simp only [if_pos he] at hoo
      have hh : scoreKey u (l+a) < scoreKey u (l+b) := by simp only [scoreKey,if_pos he]; dsimp [o] at lt; omega
      exact iff_of_false (not_lt_of_ge hh.le) (not_lt_of_ge hoo.le)
    · simp only [if_neg he] at hoo
      have hh : scoreKey u (l+b) < scoreKey u (l+a) := by
        simp only [scoreKey,if_neg he]
        dsimp [o] at lt nla nlb
        omega
      exact iff_of_true hh hoo
  · let s := anchor m o (l+a)
    have hea := anchor_eq m o (l+a) (l+b) eq
    have hs₁ := anchor_range m o (l+a) (by omega)
    have hs₂ := anchor_range m o (l+b) (by omega)
    rw [←hea] at hs₂
    have ht := transport_unordered u h s l (l+a) (l+b) hs₁.1 hl
      ⟨hs₁.2.1,hs₂.2.1,hs₁.2.2,hs₂.2.2⟩ ⟨by omega,by omega, by omega,by omega⟩
    rw [show l+a-l=a by omega,show l+b-l=b by omega] at ht
    have hanchor : anchorWord u (l+a) > anchorWord u (l+b) ↔ word (tagExt u l) a > word (tagExt u l) b := by
      unfold anchorWord
      change word (tagExt u (anchor m o (l+a))) _ > word (tagExt u (anchor m o (l+b))) _ ↔ _
      rw [←hea]
      exact ht
    unfold scoreKey
    dsimp [o] at eq
    rw [eq]
    dsimp only
    omega
  · have hoo := rowCross (tagExt u l) ⟨b,hb⟩ ⟨a,ha⟩ (by dsimp; omega)
    rw [hp.1] at hoo
    by_cases he : (row (tagExt u 0)).lane=0
    · simp only [if_pos he] at hoo
      have hh : scoreKey u (l+b) < scoreKey u (l+a) := by simp only [scoreKey,if_pos he]; dsimp [o] at gt; omega
      exact iff_of_true hh hoo
    · simp only [if_neg he] at hoo
      have hh : scoreKey u (l+a) < scoreKey u (l+b) := by
        simp only [scoreKey,if_neg he]
        dsimp [o] at gt nla nlb
        omega
      exact iff_of_false (not_lt_of_ge hh.le) (not_lt_of_ge hoo.le)

theorem scoreInjective {m : Nat} (u : Fin (m+1) → State) :
    Function.Injective (fun i : Fin (m+9) => scoreKey u i.val) := by
  intro a b he
  let o := (row (tagExt u 0)).phase
  have hA := anchor_word_range u a.val a.isLt
  have hB := anchor_word_range u b.val b.isLt
  have hAp : block o a.val ≤ m+9 := by
    unfold block; have := a.isLt; have := (labelBounds (tagExt u 0)).2
    dsimp [o]
    omega
  have hBp : block o b.val ≤ m+9 := by
    unfold block; have := b.isLt; have := (labelBounds (tagExt u 0)).2
    dsimp [o]
    omega
  have hb : block o a.val = block o b.val := by
    unfold scoreKey at he
    dsimp only at he
    dsimp [o] at hAp hBp ⊢
    split_ifs at he <;> omega
  have hh : anchorWord u a.val = anchorWord u b.val := by
    unfold scoreKey at he
    dsimp only at he
    dsimp [o] at hb
    rw [hb] at he
    omega
  have anc := anchor_eq m o a.val b.val hb
  have ra := anchor_range m o a.val a.isLt
  have rb := anchor_range m o b.val b.isLt
  rw [←anc] at rb
  let r : Fin 9 := ⟨a.val-anchor m o a.val,by omega⟩
  let s : Fin 9 := ⟨b.val-anchor m o a.val,by omega⟩
  have hword : word (tagExt u (anchor m o a.val)) r.val = word (tagExt u (anchor m o a.val)) s.val := by
    unfold anchorWord at hh
    dsimp only [o] at *
    rw [←anc] at hh
    exact hh
  have ht := congrArg Fin.val (injective_word _ _ _ hword)
  apply Fin.ext
  dsimp [r,s] at ht
  omega

theorem realizes {m : Nat} (u : Fin (m+1) → State) (h : WalkValid m u) :
    ∃ f : Perm (m+9), ∀ l≤m, Matches (ext f) l (tagExt u l) := by
  obtain ⟨f,hf⟩ := rank_exists _ (scoreInjective u)
  refine ⟨f,?_⟩
  intro l hl a ha b hb
  have ha' : l+a<m+9 := by omega
  have hb' : l+b<m+9 := by omega
  have hh := (scoreMatches u h l hl) a ha b hb
  simp [ext,ha',hb',gt_iff_lt,←Fin.lt_def]
  exact (hf ⟨l+b,hb'⟩ ⟨l+a,ha'⟩).trans hh

end Nonconv
