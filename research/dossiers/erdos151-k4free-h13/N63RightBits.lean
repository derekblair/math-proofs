import N63CodeFilters
import N63MaskNormalize
import Init.Data.Nat.Bitwise.Lemmas

namespace Erdos151N63

def edgeBits (u : Nat) (r : Nat) (p : Nat×Nat) : Nat :=
  if p.1=u then r ||| (1 <<< p.2) else if p.2=u then r ||| (1 <<< p.1) else r

theorem edgeBits_fold_bit (L : List (Nat×Nat)) (u j r : Nat) :
    (L.foldl (edgeBits u) r).testBit j =
      (r.testBit j || decide ((u,j) ∈ L ∨ (j,u) ∈ L)) := by
  induction L generalizing r with
  | nil => simp
  | cons p L ih =>
    rcases p with ⟨a,b⟩
    rw [List.foldl_cons, ih]
    simp only [edgeBits, List.mem_cons, Prod.mk.injEq]
    by_cases h : a=u
    · subst a
      simp only [true_and, if_true, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
        Nat.testBit_two_pow]
      by_cases bj : b=j <;> by_cases ju : j=u <;>
        simp_all [Bool.or_assoc,or_assoc,eq_comm]
    · by_cases hb : b=u
      · subst b
        simp only [if_neg h, if_true, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
        by_cases aj : a=j <;> simp_all [Bool.or_assoc,or_assoc,eq_comm]
      · simp [h,hb,Ne.symm h,Ne.symm hb]

def codeEdges (q h : Nat) : List (Nat×Nat) :=
  (((pairs q).zipIdx.filter fun p => h.testBit p.2).map Prod.fst)

theorem rightBits_adj (q h u j : Nat) (hu : u < q) :
    adj (graphOfCode q h) u j = true ↔ (u,j) ∈ codeEdges q h ∨ (j,u) ∈ codeEdges q h := by
  have hm : mask (graphOfCode q h) u = (codeEdges q h).foldl (edgeBits u) 0 := by
    simp [mask,graphOfCode,codeEdges,hu]; rfl
  rw [adj,hm,edgeBits_fold_bit]
  simp


theorem codeEdges_subset_pairs {q h : Nat} {p : Nat×Nat} (hp : p ∈ codeEdges q h) :
    p ∈ pairs q := by
  obtain ⟨⟨e,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hi).1)

theorem rightBits_width (q h u : Nat) (hu : u < q) :
    mask (graphOfCode q h) u < 2^q := by
  by_contra! hbig
  obtain ⟨j,hj,hb⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hbig
  change adj (graphOfCode q h) u j = true at hb
  rcases (rightBits_adj q h u j hu).mp hb with hE|hE
  · have hj' := ((mem_pairs_iff q u j).mp (codeEdges_subset_pairs hE)).2.1
    omega
  · have hj' := ((mem_pairs_iff q j u).mp (codeEdges_subset_pairs hE)).1
    omega

theorem right_code_exists (q : Nat) (R : Nat → Nat → Bool)
    (sym : ∀ i j, R i j = R j i) (irr : ∀ i, R i i = false) :
    ∃ h < 2^(pairs q).length, ∀ i < q, ∀ j < q, adj (graphOfCode q h) i j = R i j := by
  let L := pairs q
  let F (i : Fin L.length) : Bool := R (L[i.val]).1 (L[i.val]).2
  let h := (bitsOf L.length F).toNat
  have hchar : ∀ a b, (a,b) ∈ codeEdges q h ↔ (a,b) ∈ L ∧ R a b = true := by
    intro a b
    constructor
    · intro hmem
      obtain ⟨⟨e,i⟩,hi,he⟩ := List.mem_map.mp hmem
      have hzip := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp hi).1
      have hlt := List.getElem?_eq_some_iff.mp hzip
      obtain ⟨hil,heq⟩ := hlt
      have hb := (List.mem_filter.mp hi).2
      change (bitsOf L.length F).toNat.testBit i = true at hb
      have hh := bitsOf_reads L.length F ⟨i,hil⟩
      change (bitsOf L.length F).toNat.testBit i = R (L[i]'hil).1 (L[i]'hil).2 at hh
      change e = (a,b) at he
      rw [heq,he] at hh
      exact ⟨List.mem_of_getElem (heq.trans he), hh.symm.trans hb⟩
    · rintro ⟨hp,hR⟩
      obtain ⟨i,hi,he⟩ := List.getElem_of_mem hp
      refine List.mem_map.mpr ⟨((a,b),i),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
      · apply List.mk_mem_zipIdx_iff_getElem?.mpr
        exact List.getElem?_eq_some_iff.mpr ⟨hi,he⟩
      · change (bitsOf L.length F).toNat.testBit i = true
        have hh := bitsOf_reads L.length F ⟨i,hi⟩
        change (bitsOf L.length F).toNat.testBit i = R (L[i]'hi).1 (L[i]'hi).2 at hh
        rw [hh,he]
        exact hR
  refine ⟨h,(bitsOf L.length F).isLt,?_⟩
  intro i hi j hj
  by_cases hin : i=j
  · subst j
    have hfalse : ¬adj (graphOfCode q h) i i = true := by
      intro hh
      rcases (rightBits_adj q h i i hi).mp hh with hE|hE <;>
        exact Bool.false_ne_true ((irr i).symm.trans ((hchar i i).mp hE).2)
    rw [Bool.eq_false_of_not_eq_true hfalse, irr]
  · apply Bool.eq_iff_iff.mpr
    rw [rightBits_adj q h i j hi, hchar, hchar]
    rw [sym j i]
    constructor
    · exact fun hh => hh.elim And.right And.right
    · intro hR
      by_cases hij : i < j
      · exact Or.inl ⟨(mem_pairs_iff q i j).mpr ⟨hi,hj,hij⟩,hR⟩
      · exact Or.inr ⟨(mem_pairs_iff q j i).mpr ⟨hj,hi,by omega⟩,hR⟩

#print axioms rightBits_width
#print axioms right_code_exists

theorem pairs_length_small (q : Nat) (hq : q≤4) :
    (pairs q).length = q*(q-1)/2 := by
  have h : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- Obtain both the bounded right-block code and its exact decoding,
ready for the finite d/h census. -/
theorem right_code_nine (d : Nat) (hd : 4≤d) (hd' : d≤8) (R : Nat → Nat → Bool)
    (sym : ∀ i j, R i j = R j i) (irr : ∀ i, R i i = false) :
    ∃ h < 2^((8-d)*(7-d)/2), ∀ i < 8-d, ∀ j < 8-d,
      adj (graphOfCode (8-d) h) i j = R i j := by
  obtain ⟨h,hb,hr⟩ := right_code_exists (8-d) R sym irr
  rw [pairs_length_small _ (by omega),show 8-d-1=7-d by omega] at hb
  exact ⟨h,hb,hr⟩

#print axioms right_code_nine
end Erdos151N63
