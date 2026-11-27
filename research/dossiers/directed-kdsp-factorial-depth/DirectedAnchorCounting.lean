import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

open scoped BigOperators
namespace DirectedKDSP

variable {C D : Type*} [DecidableEq C] {L : ℕ}

structure AnchoredBlocks (C D : Type*) (L : ℕ) where
  support : C → Finset D
  active : Fin L → Finset D
  first : Fin L → D → ℕ
  last : Fin L → D → ℕ
  direction : Fin L → D → Bool
  witness : Fin L → C
  sign : Fin L → Bool

def fiber (A : AnchoredBlocks C D L) (c : C) (s : Bool) : Finset (Fin L) :=
  Finset.univ.filter fun d => A.witness d = c ∧ A.sign d = s

/-- Each earlier block is separated from the entire later active suffix
on each of its active chains, with one fixed comparison direction. -/
def SuffixSeparated (A : AnchoredBlocks C D L) : Prop :=
  ∀ d e, d < e → ∀ i, i ∈ A.active d → i ∈ A.active e →
    if A.direction d i then A.last d i < A.first e i else A.last e i < A.first d i

def MonochromaticWitness (A : AnchoredBlocks C D L) : Prop :=
  ∀ d, ∀ i ∈ A.support (A.witness d),
    i ∈ A.active d ∧ A.direction d i = A.sign d

/-- Abstract input from Cao–Qi–Wang Lemma 7.2. The witness labels denote
strictly cheaper cyclic permutations; `support` is the moved chain set.
No cost computation or Section 10 scheduling claim is encoded here. -/
def NoAlignedRepeat (A : AnchoredBlocks C D L) : Prop :=
  ∀ c (b : Fin (A.support c).card → Fin L), Function.Injective b →
    (∀ t, A.witness (b t) = c) →
    (∀ t u, t < u → ∀ i ∈ A.support c, A.last (b t) i < A.first (b u) i) →
    False

theorem pair_aligned (A : AnchoredBlocks C D L)
    (sep : SuffixSeparated A) (mono : MonochromaticWitness A)
    (c : C) (s : Bool) {d e : Fin L}
    (hd : d ∈ fiber A c s) (he : e ∈ fiber A c s) (hlt : d < e)
    (i : D) (hi : i ∈ A.support c) :
    if s then A.last d i < A.first e i else A.last e i < A.first d i := by
  obtain ⟨dw,ds⟩ := (Finset.mem_filter.mp hd).2
  obtain ⟨ew,_⟩ := (Finset.mem_filter.mp he).2
  have a := mono d i (dw.symm ▸ hi)
  have b := mono e i (ew.symm ▸ hi)
  have h := sep d e hlt i a.1 b.1
  rwa [a.2,ds] at h

theorem aligned_of_large_fiber (A : AnchoredBlocks C D L)
    (sep : SuffixSeparated A) (mono : MonochromaticWitness A)
    (c : C) (s : Bool) (hlarge : (A.support c).card ≤ (fiber A c s).card) :
    ∃ b : Fin (A.support c).card → Fin L, Function.Injective b ∧
      (∀ t, A.witness (b t)=c) ∧
      (∀ t u, t<u → ∀ i ∈ A.support c, A.last (b t) i < A.first (b u) i) := by
  let S := fiber A c s
  let f (j : Fin (A.support c).card) := S.orderEmbOfFin rfl (Fin.castLE hlarge j)
  have mf (j : Fin (A.support c).card) : f j ∈ fiber A c s :=
    Finset.orderEmbOfFin_mem S rfl (Fin.castLE hlarge j)
  have fs : StrictMono f := by
    intro a b h
    exact (S.orderEmbOfFin rfl).strictMono h
  cases s
  · refine ⟨fun t => f t.rev, fs.injective.comp Fin.rev_injective, ?_, ?_⟩
    · intro t
      exact (Finset.mem_filter.mp (mf t.rev)).2.1
    · intro t u h i hi
      have H := fs (Fin.rev_lt_rev.mpr h)
      simpa using pair_aligned A sep mono c false (mf u.rev) (mf t.rev) H i hi
  · refine ⟨f,fs.injective,?_ ,?_⟩
    · exact fun t => (Finset.mem_filter.mp (mf t)).2.1
    · intro t u h i hi
      simpa using pair_aligned A sep mono c true (mf t) (mf u) (fs h) i hi

theorem fiber_cap (A : AnchoredBlocks C D L)
    (sep : SuffixSeparated A) (mono : MonochromaticWitness A)
    (no : NoAlignedRepeat A) (c : C) (s : Bool) :
    (fiber A c s).card ≤ (A.support c).card - 1 := by
  by_contra! h
  have hh : (A.support c).card ≤ (fiber A c s).card := by omega
  obtain ⟨b,inj,w,order⟩ := aligned_of_large_fiber A sep mono c s hh
  exact no c b inj w order

theorem signed_count [Fintype C] (A : AnchoredBlocks C D L)
    (sep : SuffixSeparated A) (mono : MonochromaticWitness A)
    (no : NoAlignedRepeat A) :
    L ≤ ∑ c : C, 2*((A.support c).card - 1) := by
  let f (d : Fin L) : C×Bool := (A.witness d,A.sign d)
  have h : (Finset.univ : Finset (Fin L)).card =
      ∑ p : C×Bool, ((Finset.univ : Finset (Fin L)).filter (fun d => f d=p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun d _ => Finset.mem_univ (f d))
  have E (p : C×Bool) : (Finset.univ.filter (fun d => f d=p)) = fiber A p.1 p.2 := by
    ext d
    simp [fiber,f,Prod.ext_iff]
  simp only [Finset.card_univ,Fintype.card_fin,E] at h
  calc
    _ = ∑ p : C×Bool, (fiber A p.1 p.2).card := h
    _ ≤ ∑ p : C×Bool, ((A.support p.1).card - 1) :=
      Finset.sum_le_sum (fun p _ => fiber_cap A sep mono no p.1 p.2)
    _ = _ := by
      rw [← Finset.univ_product_univ,Finset.sum_product]
      simp [Finset.sum_const]

theorem uniform_count [Fintype C] (A : AnchoredBlocks C D L)
    (sep : SuffixSeparated A) (mono : MonochromaticWitness A)
    (no : NoAlignedRepeat A) (k : ℕ) (hk : ∀ c, (A.support c).card ≤ k) :
    L ≤ 2*(k-1)*Fintype.card C := by
  refine (signed_count A sep mono no).trans ?_
  have H := Finset.sum_le_sum (s := (Finset.univ : Finset C))
    (fun c _ => Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right (hk c) 1))
  simpa [Finset.sum_const,Nat.nsmul_eq_mul,mul_comm] using H

#print axioms aligned_of_large_fiber
#print axioms signed_count
#print axioms uniform_count
end DirectedKDSP
