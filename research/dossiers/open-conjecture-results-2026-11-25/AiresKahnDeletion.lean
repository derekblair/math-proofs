import Mathlib

/-!
Counterexample to both parts of Conjecture 12.5 of Max Aires and Jeff Kahn,
"Balancing extensions in posets of large width", arXiv:2509.11549v1, §12.
https://arxiv.org/html/2509.11549v1#S12

Poset P: chains A_1<...<A_30 and B_1<...<B_77 with the only additional
generating comparisons A_8 < x < B_25. The induced deletion keeps
A_8 < B_25. An ordinary linear extension is determined by the ranks of
the A-chain elements and the distinguished separator; the B elements
take the other ranks in increasing order. The separator is x before
deletion and A_8 after deletion. StandardRanks describes these complete
uncompressed rank layouts; toStandard_bijective proves exact enumeration.
The complementary constraints on prefix counts ensure the bridge
comparisons, and withRanks_order/withoutRanks_order verify those
comparisons directly on the sorted ranks. The two strict inequalities
are checked over the exact uniform rank means, using rational arithmetic.

Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/
namespace AiresKahnDeletion

abbrev Shuffle (L k : Nat) := {p : Finset (Fin L) // p.card=k}
def score {L k : Nat} (p : Shuffle L k) : Nat :=
  ∑ i ∈ p.val, (i.val+1)

def shuffleEquiv (L k : Nat) :
    Shuffle L k ≃ ↥((Finset.univ : Finset (Fin L)).powersetCard k) where
  toFun p := ⟨p.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,p.property⟩⟩
  invFun p := ⟨p.val,(Finset.mem_powersetCard.mp p.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem shuffle_count (L k : Nat) : Fintype.card (Shuffle L k)=L.choose k := by
  rw [Fintype.card_congr (shuffleEquiv ..)]
  simp

def reflected {L k : Nat} (p : Shuffle L k) : Shuffle L k :=
  ⟨p.val.map (Fin.revPerm : Fin L ≃ Fin L).toEmbedding,by simp [p.property]⟩

theorem reflect_involutive {L k : Nat} : Function.Involutive (@reflected L k) := by
  intro p
  apply Subtype.ext
  ext i
  simp only [reflected,Finset.mem_map,Equiv.toEmbedding_apply,Fin.revPerm_apply]
  constructor
  · rintro ⟨a,⟨b,hb,he⟩,hh⟩
    subst a
    change b.rev.rev=i at hh
    rw [← hh,Fin.rev_rev]
    exact hb
  · intro hi
    exact ⟨i.rev,⟨i,hi,rfl⟩,Fin.rev_rev i⟩

def reflection (L k : Nat) : Shuffle L k ≃ Shuffle L k :=
  (reflect_involutive (L:=L) (k:=k)).toPerm _

theorem twice_score {L k : Nat} (p : Shuffle L k) :
    score p+score (reflected p)=k*(L+1) := by
  calc
    score p+score (reflected p) = ∑ i ∈ p.val, ((i.val+1)+(i.rev.val+1)) := by
      simp only [score,reflected,Finset.sum_map,Finset.sum_add_distrib,Equiv.toEmbedding_apply,Fin.revPerm_apply]
    _ = ∑ _i ∈ p.val, (L+1) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      change (i.val+1)+((Fin.rev i).val+1)=L+1
      simp only [Fin.val_rev]
      omega
    _ = _ := by simp [p.property]

theorem shuffle_total_score (L k : Nat) :
    2*(∑ p : Shuffle L k, score p)=L.choose k*(k*(L+1)) := by
  classical
  have h : (∑ p : Shuffle L k, score (reflected p))=(∑ p : Shuffle L k, score p) := by
    exact Equiv.sum_comp (reflection ..) score
  calc
    _ = (∑ p : Shuffle L k, score p)+(∑ p : Shuffle L k, score (reflected p)) := by rw [h]; omega
    _ = ∑ _p : Shuffle L k, (k*(L+1)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => twice_score p)
    _ = _ := by simp

end AiresKahnDeletion

namespace AiresKahnDeletion

def fastChoose (n k : Nat) : Nat :=
  if k≤n then n.factorial/(k.factorial*(n-k).factorial) else 0

theorem fastChoose_eq (n k : Nat) : fastChoose n k = n.choose k := by
  by_cases h : k≤n
  · simp only [fastChoose,ite_eq_left h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [fastChoose,ite_eq_right h,Nat.choose_eq_zero_of_lt (show n<k by omega)]

/-- Integer aggregate data: count, twice the sum of all A ranks, and
twice the sum of all literal separator ranks. -/
structure Data where
  count : Nat
  twiceA : Nat
  twiceX : Nat
deriving DecidableEq

def Data.add (a b : Data) : Data :=
  ⟨a.count+b.count,a.twiceA+b.twiceA,a.twiceX+b.twiceX⟩

def withMarkerTerm (m b i j : Nat) : Data :=
  let L := i+j
  let R := m+b-L
  let c := fastChoose L i * fastChoose R (m-i)
  ⟨c,c*(i*(L+1)+(m-i)*(2*(L+1)+R+1)),c*(2*(L+1))⟩

def removedTerm (m b s j : Nat) : Data :=
  let L := s-1+j
  let R := m+b-1-L
  let c := fastChoose L (s-1) * fastChoose R (m-s)
  ⟨c,c*((s-1)*(L+1)+2*(L+1)+(m-s)*(2*(L+1)+R+1)),0⟩

def withMarkerData (m b s t : Nat) : Data :=
  ((List.range (m+1-s)).flatMap (fun i => (List.range t).map
    (fun j => withMarkerTerm m b (s+i) j))).foldl Data.add ⟨0,0,0⟩

def removedData (m b s t : Nat) : Data :=
  ((List.range t).map (removedTerm m b s)).foldl Data.add ⟨0,0,0⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_withMarker :
    withMarkerData 30 77 8 25 =
      ⟨2655153740844032636245476816,8193247745616990427137980710536,
        159604278970615982532666489528⟩ := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_removed :
    removedData 30 77 8 25 =
      ⟨239774841209128344499110536,753843754921957433678493656640,0⟩ := by decide

end AiresKahnDeletion

namespace AiresKahnDeletion

def pairScore {L R i j : Nat}
    (shift : Nat) (p : Shuffle L i × Shuffle R j) : Nat :=
  score p.1 + score p.2 + shift

theorem pair_twice_sum (L R i j shift : Nat) :
    2*(∑ p : Shuffle L i × Shuffle R j, pairScore shift p) =
      (L.choose i*R.choose j)*(i*(L+1)+j*(R+1)+2*shift) := by
  classical
  let refl := Equiv.prodCongr (reflection L i) (reflection R j)
  have hsum : (∑ p : Shuffle L i × Shuffle R j, pairScore shift (refl p)) =
      ∑ p : Shuffle L i × Shuffle R j, pairScore shift p :=
    Equiv.sum_comp refl _
  let C := i*(L+1)+j*(R+1)+2*shift
  calc
    _ = (∑ p : Shuffle L i × Shuffle R j, pairScore shift p) +
      (∑ p : Shuffle L i × Shuffle R j, pairScore shift (refl p)) := by rw [hsum]; omega
    _ = ∑ _p : Shuffle L i × Shuffle R j, C := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      have hl := twice_score p.1
      have hr := twice_score p.2
      change score p.1+score p.2+shift +
        (score (reflected p.1)+score (reflected p.2)+shift)=C
      dsimp [C]
      omega
    _ = _ := by simp [C]

def witnessT : Nat := 2655153740844032636245476816
def witnessU : Nat := 239774841209128344499110536
def witnessA : Nat := 4096623872808495213568990355268
def witnessB : Nat := 11451808906314172892105552938944
def witnessX : Nat := 79802139485307991266333244764
def witnessa : Nat := 376921877460978716839246828320
def witnessb : Nat := 1008497155045364857676613848688

theorem rank_sum_certificate :
    witnessB*witnessU > witnessb*witnessT + 107*witnessT*witnessU := by decide

theorem normalized_certificate :
    witnessB*witnessU*108 + witnessa*witnessT*109 >
    witnessb*witnessT*109 + witnessA*witnessU*108 + 107*witnessT*witnessU*108 := by decide

theorem total_rank_check :
    witnessA+witnessB+witnessX = 5886*witnessT ∧
      witnessa+witnessb=5778*witnessU := by decide

end AiresKahnDeletion

namespace AiresKahnDeletion

abbrev Marked (m b s t : Nat) :=
  Σ i : Fin (m+1-s), Σ j : Fin t,
    Shuffle (s+i.val+j.val) (s+i.val) ×
      Shuffle (m+b-(s+i.val+j.val)) (m-(s+i.val))

abbrev Removed (m b s t : Nat) :=
  Σ j : Fin t,
    Shuffle (s-1+j.val) (s-1) ×
      Shuffle (m+b-1-(s-1+j.val)) (m-s)

def markedAScore {m b s t : Nat} (e : Marked m b s t) : Nat :=
  let i := s+e.1.val
  let j := e.2.1.val
  pairScore ((m-i)*(i+j+1)) e.2.2

def markedXScore {m b s t : Nat} (e : Marked m b s t) : Nat :=
  s+e.1.val+e.2.1.val+1

def removedAScore {m b s t : Nat} (e : Removed m b s t) : Nat :=
  let L := s-1+e.1.val+1
  pairScore (L+(m-s)*L) e.2

theorem doubleRange (a b : Nat) (f : Nat→Nat→Nat) :
    (∑ i : Fin a, ∑ j : Fin b, f i.val j.val) =
      ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin b, f i j.val)]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (fun j => f i j) b

theorem marked_count (m b s t : Nat) :
    Fintype.card (Marked m b s t) =
      ∑ i ∈ Finset.range (m+1-s), ∑ j ∈ Finset.range t,
        (withMarkerTerm m b (s+i) j).count := by
  simp only [Marked,Fintype.card_sigma,Fintype.card_prod,shuffle_count,
    withMarkerTerm,fastChoose_eq]
  exact doubleRange (m+1-s) t (fun i j =>
    (s+i+j).choose (s+i)*(m+b-(s+i+j)).choose (m-(s+i)))

theorem removed_count (m b s t : Nat) :
    Fintype.card (Removed m b s t) =
      ∑ j ∈ Finset.range t, (removedTerm m b s j).count := by
  simp only [Removed,Fintype.card_sigma,Fintype.card_prod,shuffle_count,
    removedTerm,fastChoose_eq]
  exact Fin.sum_univ_eq_sum_range (fun j => ((s-1+j).choose (s-1)) * ((m+b-1-(s-1+j)).choose (m-s))) _

theorem marked_twice (m b s t : Nat) :
    2*(∑ e : Marked m b s t, markedAScore e) =
      ∑ i ∈ Finset.range (m+1-s), ∑ j ∈ Finset.range t,
        (withMarkerTerm m b (s+i) j).twiceA := by
  classical
  rw [Fintype.sum_sigma,Finset.mul_sum]
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  rw [← doubleRange]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [withMarkerTerm]
  dsimp [markedAScore]
  rw [← Finset.mul_sum,pair_twice_sum,fastChoose_eq,fastChoose_eq]
  ring

theorem removed_twice (m b s t : Nat) :
    2*(∑ e : Removed m b s t, removedAScore e) =
      ∑ j ∈ Finset.range t, (removedTerm m b s j).twiceA := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun j => (removedTerm m b s j).twiceA)]
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [removedTerm]
  dsimp [removedAScore]
  rw [pair_twice_sum,fastChoose_eq,fastChoose_eq]
  ring

theorem marked_doubleX (m b s t : Nat) :
    2*(∑ e : Marked m b s t, markedXScore e) =
      ∑ i ∈ Finset.range (m+1-s), ∑ j ∈ Finset.range t,
        (withMarkerTerm m b (s+i) j).twiceX := by
  classical
  rw [Fintype.sum_sigma,Finset.mul_sum]
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  rw [← doubleRange]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [withMarkerTerm]
  simp [markedXScore,fastChoose_eq]

end AiresKahnDeletion

namespace AiresKahnDeletion

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_marked_count : Fintype.card (Marked 30 77 8 25)=witnessT := by
  rw [marked_count]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_removed_count : Fintype.card (Removed 30 77 8 25)=witnessU := by
  rw [removed_count]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_marked_A : (∑ e : Marked 30 77 8 25, markedAScore e)=witnessA := by
  have h := marked_twice 30 77 8 25
  have h' : (∑ i ∈ Finset.range (30+1-8), ∑ j ∈ Finset.range 25,
      (withMarkerTerm 30 77 (8+i) j).twiceA)=2*witnessA := by decide
  omega

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_removed_A : (∑ e : Removed 30 77 8 25, removedAScore e)=witnessa := by
  have h := removed_twice 30 77 8 25
  have h' : (∑ j ∈ Finset.range 25, (removedTerm 30 77 8 j).twiceA)=2*witnessa := by decide
  omega

set_option maxRecDepth 50000 in
set_option maxHeartbeats 10000000 in
theorem concrete_marked_X : (∑ e : Marked 30 77 8 25, markedXScore e)=witnessX := by
  have h := marked_doubleX 30 77 8 25
  have h' : (∑ i ∈ Finset.range (30+1-8), ∑ j ∈ Finset.range 25,
      (withMarkerTerm 30 77 (8+i) j).twiceX)=2*witnessX := by decide
  omega

end AiresKahnDeletion

namespace AiresKahnDeletion

/-- Non-separator positions, labeled A if selected and B otherwise.
The sum type tags the positions before and after the separator. -/
abbrev Layout (L R i j : Nat) :=
  {p : Finset (Fin L ⊕ Fin R) // p.toLeft.card=i ∧ p.toRight.card=j}

def asLayout {L R i j : Nat} : (Shuffle L i × Shuffle R j) ≃ Layout L R i j where
  toFun p := ⟨p.1.val.disjSum p.2.val,
    by simp only [Finset.toLeft_disjSum,Finset.toRight_disjSum,p.1.property,p.2.property,and_self]⟩
  invFun p := (⟨p.val.toLeft,p.property.1⟩,⟨p.val.toRight,p.property.2⟩)
  left_inv _ := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  right_inv p := by
    apply Subtype.ext
    ext a
    cases a <;> simp

def rankAt {L R : Nat} : Fin L ⊕ Fin R → Nat
  | .inl i => i.val+1
  | .inr j => L+1+j.val+1

def sumARanks {L R i j : Nat} (p : Layout L R i j) : Nat :=
  ∑ a ∈ p.val, rankAt a

theorem layout_rank_eq {L R i j : Nat} (p : Shuffle L i × Shuffle R j) :
    sumARanks (asLayout p) = pairScore (j*(L+1)) p := by
  change (∑ a ∈ p.1.val.disjSum p.2.val, rankAt a) = _
  rw [Finset.sum_disjSum]
  simp only [rankAt,score,pairScore]
  have hx : (∑ x ∈ p.2.val, (L+1+x.val+1)) =
      (∑ x ∈ p.2.val, (x.val+1)) + j*(L+1) := by
    calc
      _ = ∑ x ∈ p.2.val, ((x.val+1)+(L+1)) := by
        apply Finset.sum_congr rfl
        intro x _
        omega
      _ = _ := by simp [Finset.sum_add_distrib,p.2.property]
  rw [hx]
  omega

end AiresKahnDeletion

namespace AiresKahnDeletion

def cutEquiv (N l : Nat) (h : l≤N) : Fin l ⊕ Fin (N-l) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

theorem cut_left {N l : Nat} (h : l≤N) (i : Fin l) :
    (cutEquiv N l h (.inl i)).val=i.val := by
  simp [cutEquiv,finSumFinEquiv_apply_left]

theorem cut_right {N l : Nat} (h : l≤N) (i : Fin (N-l)) :
    (cutEquiv N l h (.inr i)).val=l+i.val := by
  simp [cutEquiv,finSumFinEquiv_apply_right]

theorem cut_prefix_eq {N l : Nat} (h : l≤N) (p : Finset (Fin l ⊕ Fin (N-l))) :
    ((p.map (cutEquiv N l h).toEmbedding).filter (fun i => i.val<l)).card = p.toLeft.card := by
  classical
  let E := cutEquiv N l h
  let b : Fin l ↪ Fin N := ⟨fun i => E (.inl i), by
    intro i j he
    exact Sum.inl.inj (E.injective he)⟩
  have he : (p.map E.toEmbedding).filter (fun i => i.val<l) = p.toLeft.map b := by
    ext a
    constructor
    · intro hx
      obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hx
      obtain ⟨i,hi,hi'⟩ := Finset.mem_map.mp hs
      change E i=a at hi'
      cases i with
      | inl j => exact Finset.mem_map.mpr ⟨j,Finset.mem_toLeft.mpr hi,hi'⟩
      | inr j =>
        have hval := cut_right h j
        change (cutEquiv N l h (.inr j)).val=l+j.val at hval
        have hh : (cutEquiv N l h (.inr j)).val=a.val := congrArg Fin.val hi'
        omega
    · intro hx
      obtain ⟨j,hj,he⟩ := Finset.mem_map.mp hx
      have hj' := Finset.mem_toLeft.mp hj
      have he' : E (.inl j)=a := he
      have hv := cut_left h j
      have hval : (cutEquiv N l h (.inl j)).val=a.val := congrArg Fin.val he'
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨.inl j,hj',he'⟩,by have hlt := j.isLt; omega⟩
  rw [he,Finset.card_map]

theorem uncut_prefix_eq {N l : Nat} (h : l≤N) (p : Finset (Fin N)) :
    (p.map (cutEquiv N l h).symm.toEmbedding).toLeft.card =
      (p.filter (fun i => i.val<l)).card := by
  have hp := cut_prefix_eq h (p.map (cutEquiv N l h).symm.toEmbedding)
  have he : (p.map (cutEquiv N l h).symm.toEmbedding).map (cutEquiv N l h).toEmbedding = p := by
    ext i
    simp
  rw [he] at hp
  exact hp.symm

theorem prefix_card_bound {N l : Nat} (p : Finset (Fin N)) (h : l≤N) :
    (p.filter (fun i => i.val<l)).card≤l := by
  rw [← uncut_prefix_eq h]
  simpa using Finset.card_le_univ (p.map (cutEquiv N l h).symm.toEmbedding).toLeft

end AiresKahnDeletion

namespace AiresKahnDeletion

def countBefore {N : Nat} (p : Finset (Fin N)) (l : Nat) : Nat :=
  (p.filter (fun i => i.val<l)).card

def fullRank {N : Nat} (l : Nat) (i : Fin N) : Nat :=
  if i.val<l then i.val+1 else i.val+2

theorem rank_transported {N l : Nat} (h : l≤N) (a : Fin l ⊕ Fin (N-l)) :
    fullRank l (cutEquiv N l h a) = rankAt a := by
  cases a with
  | inl i =>
    rw [fullRank,cut_left]
    exact ite_eq_left i.isLt
  | inr i =>
    rw [fullRank,cut_right,ite_eq_right (by omega : ¬l+i.val<l)]
    change l+i.val+2=l+1+i.val+1
    omega

theorem score_transported {N l : Nat} (h : l≤N) (p : Finset (Fin l ⊕ Fin (N-l))) :
    (∑ i ∈ p.map (cutEquiv N l h).toEmbedding, fullRank l i) =
      ∑ a ∈ p, rankAt a := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl (fun a _ => rank_transported h a)

theorem cut_card {N l : Nat} (h : l≤N) (p : Finset (Fin N)) :
    let z := p.map (cutEquiv N l h).symm.toEmbedding
    z.toLeft.card+z.toRight.card=p.card := by
  let z := p.map (cutEquiv N l h).symm.toEmbedding
  have he : z.toLeft.disjSum z.toRight=z := by ext a; cases a <;> simp
  change z.toLeft.card+z.toRight.card=p.card
  rw [← Finset.card_disjSum,he,Finset.card_map]
    

theorem map_cut_inverse1 {N l : Nat} (h : l≤N) (p : Finset (Fin N)) :
    (p.map (cutEquiv N l h).symm.toEmbedding).map (cutEquiv N l h).toEmbedding = p := by
  ext i
  simp

theorem map_cut_inverse2 {N l : Nat} (h : l≤N) (p : Finset (Fin l ⊕ Fin (N-l))) :
    (p.map (cutEquiv N l h).toEmbedding).map (cutEquiv N l h).symm.toEmbedding = p := by
  ext i
  simp

/-- Complete positional description of a linear extension of a two-chain
bridge poset. Position l (zero-based) is the distinguished separator.
The other N positions are compressed by skipping l; exactly the set p
is filled by the increasing A chain. The increasing B chain fills the
complement. The predicate ok is the condition on the numbers of A and
B predecessors of the separator. -/
structure BridgeRanks (N m : Nat) (ok : Nat→Nat→Prop) where
  l : Nat
  l_le : l≤N
  p : Finset (Fin N)
  p_card : p.card=m
  allowed : ok (countBefore p l) (l-countBefore p l)

/-- Independent shuffle choices before and after the separator. -/
abbrev BridgeCuts (N m : Nat) (ok : Nat→Nat→Prop) :=
  Σ c : {c : Nat×Nat // c.1+c.2≤N ∧ c.1 ≤ m ∧ ok c.1 c.2},
    Layout (c.val.1+c.val.2) (N-(c.val.1+c.val.2)) c.val.1 (m-c.val.1)

def cutsToRanks {N m : Nat} {ok : Nat→Nat→Prop} (d : BridgeCuts N m ok) :
    BridgeRanks N m ok := by
  let E := cutEquiv N (d.1.val.1+d.1.val.2) d.1.property.1
  have c : d.2.val.card=m := by
    have he : d.2.val.toLeft.disjSum d.2.val.toRight=d.2.val := by
      ext a; cases a <;> simp
    rw [← he,Finset.card_disjSum,d.2.property.1,d.2.property.2]
    have h := d.1.property.2.1
    omega
  have hp : countBefore (d.2.val.map E.toEmbedding) (d.1.val.1+d.1.val.2) =
      d.1.val.1 := (cut_prefix_eq d.1.property.1 d.2.val).trans d.2.property.1
  refine ⟨_,d.1.property.1,d.2.val.map E.toEmbedding,by simpa only [Finset.card_map] using c,?_⟩
  rw [hp]
  simpa using d.1.property.2.2

def ranksToCuts {N m : Nat} {ok : Nat→Nat→Prop} (d : BridgeRanks N m ok) :
    BridgeCuts N m ok := by
  let i := countBefore d.p d.l
  let j := d.l-i
  have hi : i ≤ m := (Finset.card_filter_le _ _).trans_eq d.p_card
  have hl : i≤d.l := prefix_card_bound d.p d.l_le
  have hs : i+j=d.l := by dsimp [j]; omega
  have hN : i+j ≤ N := hs.le.trans d.l_le
  let E := cutEquiv N (i+j) hN
  let z := d.p.map E.symm.toEmbedding
  have hzi : z.toLeft.card=i := by
    have h := uncut_prefix_eq hN d.p
    exact h.trans (by change countBefore d.p (i+j)=i; rw [hs])
  have hzj : z.toRight.card=m-i := by
    have h := cut_card hN d.p
    change z.toLeft.card+z.toRight.card=d.p.card at h
    rw [hzi,d.p_card] at h
    omega
  exact ⟨⟨(i,j),hN,hi,d.allowed⟩,⟨z,hzi,hzj⟩⟩

end AiresKahnDeletion

namespace AiresKahnDeletion

@[ext] theorem BridgeRanks.ext {N m : Nat} {ok : Nat→Nat→Prop}
    {x y : BridgeRanks N m ok} (hl : x.l=y.l) (hp : x.p=y.p) : x=y := by
  cases x
  cases y
  congr

theorem cuts_ranks_roundtrip {N m : Nat} {ok : Nat→Nat→Prop} (d : BridgeRanks N m ok) :
    cutsToRanks (ranksToCuts d) = d := by
  let i := countBefore d.p d.l
  let j := d.l-i
  have hi : i≤d.l := prefix_card_bound d.p d.l_le
  have hl : i+j=d.l := by dsimp [j]; omega
  apply BridgeRanks.ext
  · exact hl
  · exact map_cut_inverse1 (hl.le.trans d.l_le) d.p


theorem cuts_injective {N m : Nat} {ok : Nat→Nat→Prop} :
    Function.Injective (@cutsToRanks N m ok) := by
  intro d d' he
  rcases d with ⟨⟨⟨i,j⟩,hd⟩,⟨p,hp⟩⟩
  rcases d' with ⟨⟨⟨i',j'⟩,hd'⟩,⟨p',hp'⟩⟩
  have hN : i+j≤N := hd.1
  have hN' : i'+j'≤N := hd'.1
  let E := cutEquiv N (i+j) hN
  let E' := cutEquiv N (i'+j') hN'
  have hi : i=i' := by
    have hec := congrArg (fun g : BridgeRanks N m ok => countBefore g.p g.l) he
    change countBefore (p.map E.toEmbedding) (i+j) =
      countBefore (p'.map E'.toEmbedding) (i'+j') at hec
    exact ((cut_prefix_eq hN p).trans hp.1).symm.trans
      (hec.trans ((cut_prefix_eq hN' p').trans hp'.1))
  have hl : i+j=i'+j' := congrArg BridgeRanks.l he
  have hj : j=j' := by omega
  subst i'
  subst j'
  have hmap : p.map E.toEmbedding = p'.map E.toEmbedding := congrArg BridgeRanks.p he
  have heq := congrArg (fun q => q.map E.symm.toEmbedding) hmap
  rw [map_cut_inverse2 hN p,map_cut_inverse2 hN p'] at heq
  subst p'
  rfl

theorem ranks_cuts_roundtrip {N m : Nat} {ok : Nat→Nat→Prop} (d : BridgeCuts N m ok) :
    ranksToCuts (cutsToRanks d) = d :=
  cuts_injective (cuts_ranks_roundtrip (cutsToRanks d))

def bridgeEquiv {N m : Nat} {ok : Nat→Nat→Prop} :
    BridgeCuts N m ok ≃ BridgeRanks N m ok :=
  ⟨cutsToRanks,ranksToCuts,ranks_cuts_roundtrip,cuts_ranks_roundtrip⟩

end AiresKahnDeletion

namespace AiresKahnDeletion

def withOK (i j : Nat) : Prop := 8 ≤ i ∧ j<25
def withoutOK (i j : Nat) : Prop := i=7 ∧ j<25

abbrev WithRanks := BridgeRanks 107 30 withOK
abbrev WithoutRanks := BridgeRanks 106 29 withoutOK

def withIndex : (Σ _i : Fin (30+1-8), Fin 25) ≃
    {c : Nat×Nat // c.1+c.2 ≤ 107 ∧ c.1 ≤ 30 ∧ withOK c.1 c.2} where
  toFun g := ⟨(8+g.1.val,g.2.val),by
    have hi := g.1.isLt
    have hj := g.2.isLt
    simp only [withOK]
    omega⟩
  invFun c := ⟨⟨c.val.1-8,by have hi := c.property.2.1; omega⟩,
    ⟨c.val.2,c.property.2.2.2⟩⟩
  left_inv g := by
    rcases g with ⟨i,j⟩
    have hi : (⟨8+i.val-8,by have h := i.isLt; omega⟩ : Fin (30+1-8)) = i := by
      apply Fin.ext
      change 8+i.val-8=i.val
      omega
    simp only [hi]
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext
    · change 8+(c.val.1-8)=c.val.1
      have h := c.property.2.2.1
      omega
    · rfl

def markedToCuts : Marked 30 77 8 25 ≃ BridgeCuts 107 30 withOK :=
  (Equiv.sigmaAssoc (fun (i : Fin (30+1-8)) (j : Fin 25) =>
    Shuffle (8+i.val+j.val) (8+i.val) × Shuffle (107-(8+i.val+j.val)) (30-(8+i.val)))).symm.trans
      (Equiv.sigmaCongr withIndex (fun _ => asLayout))

def markedRankEquiv : Marked 30 77 8 25 ≃ WithRanks :=
  markedToCuts.trans bridgeEquiv

def globalA {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :=
  ∑ p ∈ e.p, fullRank e.l p

def globalX {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) := e.l+1

theorem marked_globalA (e : Marked 30 77 8 25) :
    globalA (markedRankEquiv e)=markedAScore e := by
  let L := 8+e.1.val+e.2.1.val
  have hL : L ≤ 107 := by
    have hi := e.1.isLt
    have hj := e.2.1.isLt
    dsimp [L]
    omega
  change (∑ i ∈ (asLayout e.2.2).val.map (cutEquiv 107 L hL).toEmbedding, fullRank L i) = _
  rw [score_transported]
  exact layout_rank_eq e.2.2

theorem marked_globalX (e : Marked 30 77 8 25) :
    globalX (markedRankEquiv e)=markedXScore e := rfl

end AiresKahnDeletion

namespace AiresKahnDeletion

def withoutIndex : Fin 25 ≃
    {c : Nat×Nat // c.1+c.2 ≤ 106 ∧ c.1 ≤ 29 ∧ withoutOK c.1 c.2} where
  toFun j := ⟨(7,j.val),by
    have hj := j.isLt
    simp only [withoutOK,true_and]
    omega⟩
  invFun c := ⟨c.val.2,c.property.2.2.2⟩
  left_inv _ := rfl
  right_inv c := by
    apply Subtype.ext
    exact Prod.ext c.property.2.2.1.symm rfl

def removedRankEquiv : Removed 30 77 8 25 ≃ WithoutRanks :=
  (Equiv.sigmaCongr withoutIndex (fun _ => asLayout)).trans bridgeEquiv

theorem removed_globalA (e : Removed 30 77 8 25) :
    globalA (removedRankEquiv e)+globalX (removedRankEquiv e)=removedAScore e := by
  let L := 7+e.1.val
  have hL : L ≤ 106 := by have h := e.1.isLt; dsimp [L]; omega
  change (∑ i ∈ (asLayout e.2).val.map (cutEquiv 106 L hL).toEmbedding, fullRank L i) +
        (L+1) = _
  rw [score_transported]
  change sumARanks (asLayout e.2)+(L+1) = _
  rw [layout_rank_eq]
  simp only [removedAScore,pairScore]
  dsimp [L]
  omega

def globalB {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :=
  ∑ i ∈ (Finset.univ : Finset (Fin N)) \ e.p, fullRank e.l i

theorem globalAB {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :
    globalA e+globalB e=∑ i : Fin N, fullRank e.l i := by
  unfold globalA globalB
  rw [Nat.add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ e.p)

set_option maxRecDepth 50000 in
theorem rank_sum_108 :
    ∀ l : Fin 108, (∑ i : Fin 107, fullRank l.val i)+(l.val+1)=5886 := by decide

set_option maxRecDepth 50000 in
theorem rank_sum_107 :
    ∀ l : Fin 107, (∑ i : Fin 106, fullRank l.val i)+(l.val+1)=5778 := by decide

end AiresKahnDeletion

namespace AiresKahnDeletion

def rankEmbedding (N l : Nat) : Fin N ↪ Nat :=
  ⟨fullRank l,by
    intro i j he
    apply Fin.ext
    unfold fullRank at he
    split at he <;> split at he <;> omega⟩

theorem no_separator {N l : Nat} (p : Finset (Fin N)) :
    l+1 ∉ p.map (rankEmbedding N l) := by
  intro h
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
  change fullRank l i=l+1 at hi
  unfold fullRank at hi
  split at hi <;> omega

def mapA {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) : Finset Nat :=
  e.p.map (rankEmbedding N e.l)

def mapB {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) : Finset Nat :=
  ((Finset.univ : Finset (Fin N)) \ e.p).map (rankEmbedding N e.l)

def fullRemovedA (e : WithoutRanks) : Finset Nat := insert (globalX e) (mapA e)

theorem card_mapA {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :
    (mapA e).card=m := by simp [mapA,e.p_card]

theorem card_mapB {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :
    (mapB e).card=N-m := by
  unfold mapB
  rw [Finset.card_map,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [e.p_card]

theorem card_removedA (e : WithoutRanks) : (fullRemovedA e).card=30 := by
  have hn : globalX e ∉ mapA e := no_separator (l:=e.l) e.p
  rw [fullRemovedA,Finset.card_insert_of_notMem hn,card_mapA]

def indexedRank (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) :=
  (p.orderIsoOfFin h i).val

theorem sum_indexedRank (p : Finset Nat) {k : Nat} (h : p.card=k) :
    (∑ i : Fin k, indexedRank p h i)=∑ j ∈ p, j := by
  calc
    _ = ∑ j : ↥p, j.val := Equiv.sum_comp (p.orderIsoOfFin h).toEquiv (fun j : p => j.val)
    _ = _ := by rw [Finset.univ_eq_attach]; exact Finset.sum_attach _ (fun x => x)

def rankWA (e : WithRanks) (i : Fin 30) := indexedRank (mapA e) (card_mapA e) i
def rankWB (e : WithRanks) (i : Fin 77) := indexedRank (mapB e) (card_mapB e) i
def rankRA (e : WithoutRanks) (i : Fin 30) := indexedRank (fullRemovedA e) (card_removedA e) i
def rankRB (e : WithoutRanks) (i : Fin 77) := indexedRank (mapB e) (card_mapB e) i

theorem sum_rankWA (e : WithRanks) : (∑ i, rankWA e i)=globalA e := by
  unfold rankWA
  rw [sum_indexedRank]
  unfold mapA globalA
  rw [Finset.sum_map]
  rfl

theorem sum_rankWB (e : WithRanks) : (∑ i, rankWB e i)=globalB e := by
  unfold rankWB
  rw [sum_indexedRank]
  unfold mapB globalB
  rw [Finset.sum_map]
  rfl

theorem sum_rankRA (e : WithoutRanks) : (∑ i, rankRA e i)=globalA e+globalX e := by
  unfold rankRA
  rw [sum_indexedRank]
  unfold fullRemovedA
  have hn : globalX e ∉ mapA e := no_separator (l:=e.l) e.p
  rw [Finset.sum_insert hn]
  unfold mapA globalA
  rw [Finset.sum_map, Nat.add_comm]
  rfl

theorem sum_rankRB (e : WithoutRanks) : (∑ i, rankRB e i)=globalB e := by
  unfold rankRB
  rw [sum_indexedRank]
  unfold mapB globalB
  rw [Finset.sum_map]
  rfl

end AiresKahnDeletion

namespace AiresKahnDeletion
noncomputable opaque withFintype : Fintype WithRanks := Fintype.ofEquiv _ markedRankEquiv
noncomputable opaque withoutFintype : Fintype WithoutRanks := Fintype.ofEquiv _ removedRankEquiv
noncomputable instance : Fintype WithRanks := withFintype
noncomputable instance : Fintype WithoutRanks := withoutFintype

theorem with_rank_count : Fintype.card WithRanks = witnessT :=
  (Fintype.card_congr markedRankEquiv).symm.trans concrete_marked_count

theorem without_rank_count : Fintype.card WithoutRanks = witnessU :=
  (Fintype.card_congr removedRankEquiv).symm.trans concrete_removed_count

theorem with_A_total : (∑ e : WithRanks, ∑ i, rankWA e i)=witnessA := by
  simp only [sum_rankWA]
  rw [← Equiv.sum_comp markedRankEquiv globalA]
  simpa only [marked_globalA] using concrete_marked_A

theorem without_A_total : (∑ e : WithoutRanks, ∑ i, rankRA e i)=witnessa := by
  simp only [sum_rankRA]
  rw [← Equiv.sum_comp removedRankEquiv (fun e => globalA e+globalX e)]
  simpa only [removed_globalA] using concrete_removed_A

theorem with_X_total : (∑ e : WithRanks, globalX e)=witnessX := by
  rw [← Equiv.sum_comp markedRankEquiv globalX]
  simpa only [marked_globalX] using concrete_marked_X

theorem with_B_total : (∑ e : WithRanks, ∑ i, rankWB e i)=witnessB := by
  have he (e : WithRanks) : (∑ i, rankWA e i)+(∑ i, rankWB e i)+globalX e=5886 := by
    rw [sum_rankWA,sum_rankWB,globalAB]
    exact rank_sum_108 ⟨e.l,by have hl := e.l_le; omega⟩
  have hh : (∑ e : WithRanks, ((∑ i, rankWA e i)+(∑ i, rankWB e i)+globalX e)) =
      ∑ _e : WithRanks, 5886 := by exact Finset.sum_congr rfl (fun e _ => he e)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,with_A_total,with_X_total,
    Finset.sum_const_nat (m:=5886) (fun _ _ => rfl),Finset.card_univ,with_rank_count] at hh
  rw [Nat.mul_comm witnessT 5886] at hh
  exact Nat.add_left_cancel (Nat.add_right_cancel (hh.trans total_rank_check.1.symm))

theorem without_B_total : (∑ e : WithoutRanks, ∑ i, rankRB e i)=witnessb := by
  have he (e : WithoutRanks) : (∑ i, rankRA e i)+(∑ i, rankRB e i)=5778 := by
    rw [sum_rankRA,sum_rankRB,show globalA e+globalX e+globalB e =
      globalA e+globalB e+globalX e by omega,globalAB]
    exact rank_sum_107 ⟨e.l,by have hl := e.l_le; omega⟩
  have hh : (∑ e : WithoutRanks, ((∑ i, rankRA e i)+(∑ i, rankRB e i))) =
      ∑ _e : WithoutRanks, 5778 := by exact Finset.sum_congr rfl (fun e _ => he e)
  rw [Finset.sum_add_distrib,without_A_total,
    Finset.sum_const_nat (m:=5778) (fun _ _ => rfl),Finset.card_univ,without_rank_count] at hh
  rw [Nat.mul_comm witnessU 5778] at hh
  exact Nat.add_left_cancel (hh.trans total_rank_check.2.symm)

end AiresKahnDeletion

namespace AiresKahnDeletion

/-- Uniform expected one-based rank. Rational arithmetic is exact for
a uniform measure on the finite set of linear extensions. -/
noncomputable def meanRank {E : Type} [Fintype E] (f : E→Nat) : ℚ :=
  (∑ e : E, (f e : ℚ)) / (Fintype.card E : ℚ)

theorem sumMean {E I : Type} [Fintype E] [Fintype I] (f : E→I→Nat) :
    (∑ i : I, meanRank (fun e => f e i)) =
      ((∑ e : E, ∑ i : I, f e i : Nat) : ℚ) / (Fintype.card E : ℚ) := by
  unfold meanRank
  rw [← Finset.sum_div,Finset.sum_comm]
  push_cast
  rfl

noncomputable def hWA (i : Fin 30) := meanRank (fun e => rankWA e i)
noncomputable def hWB (i : Fin 77) := meanRank (fun e => rankWB e i)
noncomputable def hRA (i : Fin 30) := meanRank (fun e => rankRA e i)
noncomputable def hRB (i : Fin 77) := meanRank (fun e => rankRB e i)

theorem hWA_sum : (∑ i, hWA i)=(witnessA:ℚ)/(witnessT:ℚ) := by
  unfold hWA
  rw [sumMean,with_A_total,with_rank_count]
theorem hWB_sum : (∑ i, hWB i)=(witnessB:ℚ)/(witnessT:ℚ) := by
  unfold hWB
  rw [sumMean,with_B_total,with_rank_count]
theorem hRA_sum : (∑ i, hRA i)=(witnessa:ℚ)/(witnessU:ℚ) := by
  unfold hRA
  rw [sumMean,without_A_total,without_rank_count]
theorem hRB_sum : (∑ i, hRB i)=(witnessb:ℚ)/(witnessU:ℚ) := by
  unfold hRB
  rw [sumMean,without_B_total,without_rank_count]

/-- A strict violation of Conjecture 12.5(a) at n=108. The two sums
run over every element other than the deleted bridge vertex. -/
theorem counterexample_12_5_a :
    (107:ℚ) <
      (∑ i : Fin 30, max (hWA i-hRA i) 0) +
      (∑ j : Fin 77, max (hWB j-hRB j) 0) := by
  have h : (107:ℚ) < ∑ j : Fin 77, (hWB j-hRB j) := by
    rw [Finset.sum_sub_distrib,hWB_sum,hRB_sum]
    norm_num [witnessB,witnessb,witnessT,witnessU]
  have hb : (∑ j : Fin 77, (hWB j-hRB j)) ≤
      ∑ j : Fin 77, max (hWB j-hRB j) 0 :=
    Finset.sum_le_sum (fun j _ => le_max_left ..)
  have ha : 0 ≤ ∑ i : Fin 30, max (hWA i-hRA i) 0 :=
    Finset.sum_nonneg (fun i _ => le_max_right ..)
  linarith only [h,ha,hb]

/-- A strict violation of Conjecture 12.5(b) for the same poset.
The normalizers 109 and 108 are |P|+1 and |P−x|+1. -/
theorem counterexample_12_5_b :
    (107:ℚ)/109 <
      (∑ i : Fin 30, |hWA i/109-hRA i/108|) +
      (∑ j : Fin 77, |hWB j/109-hRB j/108|) := by
  have h : (107:ℚ)/109 <
      (∑ j : Fin 77, (hWB j/109-hRB j/108)) -
      (∑ i : Fin 30, (hWA i/109-hRA i/108)) := by
    simp only [Finset.sum_sub_distrib,div_eq_mul_inv,← Finset.sum_mul,hWB_sum,hRB_sum,hWA_sum,hRA_sum]
    norm_num [witnessA,witnessa,witnessB,witnessb,witnessT,witnessU]
  have ha : -(∑ i : Fin 30, (hWA i/109-hRA i/108)) ≤
      ∑ i : Fin 30, |hWA i/109-hRA i/108| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun _ _ => neg_le_abs _)
  have hb : (∑ j : Fin 77, (hWB j/109-hRB j/108)) ≤
      ∑ j : Fin 77, |hWB j/109-hRB j/108| :=
    Finset.sum_le_sum (fun _ _ => le_abs_self _)
  linarith only [h,ha,hb]

end AiresKahnDeletion

#print axioms AiresKahnDeletion.counterexample_12_5_a
#print axioms AiresKahnDeletion.counterexample_12_5_b

namespace AiresKahnDeletion

theorem indexedRank_mono (p : Finset Nat) {k : Nat} (h : p.card=k) :
    StrictMono (indexedRank p h) :=
  fun _ _ hi => (p.orderIsoOfFin h).strictMono hi

theorem indexedRank_mem (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) :
    indexedRank p h i∈p := (p.orderIsoOfFin h i).property

theorem indexedRank_before (p : Finset Nat) {k : Nat} (h : p.card=k) (i : Fin k) (l : Nat) :
    indexedRank p h i < l ↔ i.val < (p.filter (·<l)).card := by
  classical
  let e := p.orderIsoOfFin h
  let F := p.filter (·<l)
  change indexedRank p h i < l ↔ i.val < F.card
  constructor
  · intro hi
    let f (j : Nat) := if hj : j<k then indexedRank p h ⟨j,hj⟩ else 0
    have hf := Finset.card_le_card_of_injOn f (s:=Finset.range (i.val+1)) (t:=F)
      (by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hk : j<k := by have ht := i.isLt; omega
        simp only [f,dite_eq_left hk]
        have hle : (⟨j,hk⟩ : Fin k) ≤ i := by exact Nat.le_of_lt_succ hj'
        exact Finset.mem_filter.mpr ⟨indexedRank_mem .., ((indexedRank_mono p h).monotone hle).trans_lt hi⟩)
      (by
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp ha
        have hb' := Finset.mem_range.mp hb
        have haK : a<k := by have hi := i.isLt; omega
        have hbK : b<k := by have hi := i.isLt; omega
        simp only [f,dite_eq_left haK,dite_eq_left hbK] at hab
        exact congrArg Fin.val ((indexedRank_mono p h).injective hab))
    rw [Finset.card_range] at hf
    omega
  · intro hc
    by_contra! hi
    let f (x : Nat) := if hx : x∈p then (e.symm ⟨x,hx⟩).val else 0
    have hf := Finset.card_le_card_of_injOn f (s:=F) (t:=Finset.range i.val)
      (by
        intro x hx
        have ⟨hm,hx'⟩ := Finset.mem_filter.mp hx
        have hxi : (e.symm ⟨x,hm⟩) < i := by
          by_contra! hh
          have hle := (indexedRank_mono p h).monotone hh
          have heq : indexedRank p h (e.symm ⟨x,hm⟩)=x := by
            change (e (e.symm ⟨x,hm⟩)).val=x
            simp
          omega
        exact Finset.mem_range.mpr (by simpa only [f,dite_eq_left hm,Fin.lt_def] using hxi))
      (by
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).1
        have hb' := (Finset.mem_filter.mp hb).1
        simp only [f,dite_eq_left ha',dite_eq_left hb'] at hab
        have hx := e.symm.injective (Fin.ext hab)
        exact congrArg Subtype.val hx)
    rw [Finset.card_range] at hf
    omega

theorem fullRank_before {N : Nat} (l : Nat) (i : Fin N) :
    fullRank l i < l+1 ↔ i.val<l := by unfold fullRank; split <;> omega

theorem fullRank_cover {N l : Nat} (h : l≤N) :
    (Finset.univ : Finset (Fin N)).map (rankEmbedding N l) =
      (Finset.Icc 1 (N+1)).erase (l+1) := by
  ext p
  simp only [Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_erase,Finset.mem_Icc]
  constructor
  · rintro ⟨i,rfl⟩
    change fullRank l i ≠ l+1 ∧ 1≤fullRank l i ∧ fullRank l i≤N+1
    have hi := i.isLt
    unfold fullRank
    split <;> omega
  · intro hp
    by_cases hl : p<l+1
    · have hpi : p-1<N := by omega
      refine ⟨⟨p-1,hpi⟩,?_⟩
      change fullRank l ⟨p-1,hpi⟩=p
      simp only [fullRank,ite_eq_left (by omega : p-1<l)]
      omega
    · have hpi : p-2<N := by omega
      refine ⟨⟨p-2,hpi⟩,?_⟩
      change fullRank l ⟨p-2,hpi⟩=p
      simp only [fullRank,ite_eq_right (by omega : ¬p-2<l)]
      omega

theorem count_mapPrefix {N : Nat} (p : Finset (Fin N)) (l : Nat) :
    ((p.map (rankEmbedding N l)).filter (·<l+1)).card = countBefore p l := by
  have he : (p.map (rankEmbedding N l)).filter (·<l+1) =
      (p.filter (fun i => i.val<l)).map (rankEmbedding N l) := by
    ext x
    constructor
    · intro h
      obtain ⟨hm,hx⟩ := Finset.mem_filter.mp h
      obtain ⟨i,hi,he⟩ := Finset.mem_map.mp hm
      change fullRank l i=x at he
      exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,(fullRank_before l i).1 (he ▸ hx)⟩,he⟩
    · intro h
      obtain ⟨i,hi,he⟩ := Finset.mem_map.mp h
      obtain ⟨hm,hl⟩ := Finset.mem_filter.mp hi
      change fullRank l i=x at he
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨i,hm,he⟩,he ▸ (fullRank_before l i).2 hl⟩
  rw [he,Finset.card_map]
  rfl

theorem count_before_complement {N l : Nat} (h : l≤N) (p : Finset (Fin N)) :
    countBefore ((Finset.univ : Finset (Fin N)) \ p) l = l-countBefore p l := by
  change ((Finset.univ \ p).filter (fun i : Fin N => i.val<l)).card =
    l-(p.filter (fun i : Fin N => i.val<l)).card
  have he : ((Finset.univ \ p).filter (fun i : Fin N => i.val<l)) =
      ((Finset.univ : Finset (Fin N)).filter (fun i => i.val<l)) \ (p.filter (fun i => i.val<l)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have hu : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val<l)).card=l := by
    have ht := uncut_prefix_eq h (Finset.univ : Finset (Fin N))
    rw [Finset.map_univ_equiv] at ht
    simpa using ht.symm
  rw [he,Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ (Finset.subset_univ _)),hu]

end AiresKahnDeletion

namespace AiresKahnDeletion

theorem withRanks_order (e : WithRanks) :
    StrictMono (rankWA e) ∧ StrictMono (rankWB e) ∧
      rankWA e (7 : Fin 30)<globalX e ∧ globalX e<rankWB e (24 : Fin 77) := by
  refine ⟨indexedRank_mono ..,indexedRank_mono ..,?_,?_⟩
  · apply (indexedRank_before _ _ _ _).2
    have h := count_mapPrefix e.p e.l
    change 7 < ((e.p.map (rankEmbedding 107 e.l)).filter (·<e.l+1)).card
    rw [h]
    exact e.allowed.1
  · have hp := count_mapPrefix ((Finset.univ : Finset (Fin 107)) \ e.p) e.l
    have he := count_before_complement e.l_le e.p
    have hno : ¬ rankWB e (24 : Fin 77)<globalX e := by
      intro hf
      have hc := (indexedRank_before _ _ _ _).1 hf
      change 24 < (((Finset.univ : Finset (Fin 107)) \ e.p).map
        (rankEmbedding 107 e.l) |>.filter (·<e.l+1)).card at hc
      rw [hp,he] at hc
      have h := e.allowed.2
      omega
    have hn : rankWB e (24 : Fin 77) ≠ globalX e := by
      intro h
      have he : rankWB e (24 : Fin 77)∈mapB e := indexedRank_mem .. 
      rw [h] at he
      exact (no_separator (l:=e.l) _) he
    omega

theorem without_A8 (e : WithoutRanks) : rankRA e (7 : Fin 30)=globalX e := by
  let S := fullRemovedA e
  let x := globalX e
  let eq := S.orderIsoOfFin (card_removedA e)
  have hx : x∈S := Finset.mem_insert_self _ _
  let j := eq.symm ⟨x,hx⟩
  have hR : rankRA e j=x := by
    change (eq (eq.symm ⟨x,hx⟩)).val=x
    simp
  have hc : (S.filter (·<x)).card=7 := by
    have hset : S.filter (·<x) = (mapA e).filter (·<x) := by
      ext i
      by_cases hi : i=x
      · simp [S,fullRemovedA,x,hi]
      · simp [S,fullRemovedA,x,hi]
    rw [hset]
    exact (count_mapPrefix e.p e.l).trans e.allowed.1
  have hd : (S.filter (·<x+1)).card=8 := by
    have hset : S.filter (·<x+1) = insert x (S.filter (·<x)) := by
      ext i
      by_cases hi : i=x
      · simp [hi,hx]
      · have he : i≤x ↔ i<x := by omega
        simp [he,hi]
    rw [hset,Finset.card_insert_of_notMem (by simp),hc]
  have h₁ : ¬ j.val<7 := by
    intro h
    have hh : j.val < (S.filter (·<x)).card := by rw [hc]; exact h
    have hlt := (indexedRank_before _ (card_removedA e) j x).2 hh
    change rankRA e j<x at hlt
    omega
  have h₂ : j.val<8 := by
    rw [← hd]
    apply (indexedRank_before _ (card_removedA e) j (x+1)).1
    change rankRA e j<x+1
    omega
  have hj : j=(7:Fin 30) := by apply Fin.ext; change j.val=7; omega
  rwa [hj] at hR

theorem withoutRanks_order (e : WithoutRanks) :
    StrictMono (rankRA e) ∧ StrictMono (rankRB e) ∧
      rankRA e (7 : Fin 30)<rankRB e (24 : Fin 77) := by
  refine ⟨indexedRank_mono ..,indexedRank_mono ..,?_⟩
  rw [without_A8 e]
  have hp := count_mapPrefix ((Finset.univ : Finset (Fin 106)) \ e.p) e.l
  have he := count_before_complement e.l_le e.p
  have hno : ¬ rankRB e (24 : Fin 77)<globalX e := by
    intro hf
    have hc := (indexedRank_before _ _ _ _).1 hf
    change 24 < (((Finset.univ : Finset (Fin 106)) \ e.p).map
      (rankEmbedding 106 e.l) |>.filter (·<e.l+1)).card at hc
    rw [hp,he] at hc
    have h := e.allowed.2
    omega
  have hn : rankRB e (24 : Fin 77) ≠ globalX e := by
    intro h
    have he : rankRB e (24 : Fin 77)∈mapB e := indexedRank_mem ..
    rw [h] at he
    exact (no_separator (l:=e.l) _) he
  omega

end AiresKahnDeletion

namespace AiresKahnDeletion

/-- Uncompressed rank representation. The separator occupies rank x.
A (excluding the separator) uses exactly the chosen ranks. B receives
all other ranks. The two chains have a unique increasing numbering. -/
structure StandardRanks (N m : Nat) (ok : Nat→Nat→Prop) where
  x : Nat
  xpos : 1≤x ∧ x≤N+1
  A : Finset Nat
  within : A ⊆ (Finset.Icc 1 (N+1)).erase x
  A_card : A.card=m
  eligible : ok (A.filter (·<x)).card (x-1-(A.filter (·<x)).card)

def toStandard {N m : Nat} {ok : Nat→Nat→Prop} (e : BridgeRanks N m ok) :
    StandardRanks N m ok := by
  have hr : 1≤e.l+1 ∧ e.l+1≤N+1 := by have h := e.l_le; omega
  have hsub : mapA e ⊆ (Finset.Icc 1 (N+1)).erase (e.l+1) := by
    rw [← fullRank_cover e.l_le]
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  have hel : ok ((mapA e).filter (·<e.l+1)).card
      (e.l+1-1-((mapA e).filter (·<e.l+1)).card) := by
    unfold mapA
    rw [count_mapPrefix,Nat.add_sub_cancel]
    exact e.allowed
  exact ⟨e.l+1,hr,mapA e,hsub,card_mapA e,hel⟩

theorem toStandard_bijective {N m : Nat} {ok : Nat→Nat→Prop} :
    Function.Bijective (@toStandard N m ok) := by
  constructor
  · intro a b h
    have hx := congrArg StandardRanks.x h
    change a.l+1=b.l+1 at hx
    have hl : a.l=b.l := by omega
    have ha := congrArg StandardRanks.A h
    change a.p.map (rankEmbedding N a.l)=b.p.map (rankEmbedding N b.l) at ha
    rw [← hl] at ha
    exact BridgeRanks.ext hl (Finset.map_injective _ ha)
  · intro d
    let L := d.x-1
    have hL : L≤N := by have h := d.xpos; dsimp [L]; omega
    have hx : L+1=d.x := by have h := d.xpos.1; dsimp [L]; omega
    let p := (Finset.univ : Finset (Fin N)).filter (fun j => fullRank L j ∈ d.A)
    have hp : p.map (rankEmbedding N L) = d.A := by
      ext n
      constructor
      · intro h
        obtain ⟨i,hi,he⟩ := Finset.mem_map.mp h
        change fullRank L i=n at he
        exact he ▸ (Finset.mem_filter.mp hi).2
      · intro hn
        have ht : n ∈ (Finset.univ : Finset (Fin N)).map (rankEmbedding N L) := by
          rw [fullRank_cover hL,hx]
          exact d.within hn
        obtain ⟨i,hi,he⟩ := Finset.mem_map.mp ht
        change fullRank L i=n at he
        exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,he.symm ▸ hn⟩,he⟩
    have hc : p.card=m := by
      rw [← Finset.card_map (rankEmbedding N L),hp,d.A_card]
    have hbefore : countBefore p L=(d.A.filter (·<d.x)).card := by
      rw [← count_mapPrefix p L,hp,hx]
    have ha : ok (countBefore p L) (L-countBefore p L) := by
      rw [hbefore]
      exact d.eligible
    refine ⟨⟨L,hL,p,hc,ha⟩,?_⟩
    cases d
    simp only [toStandard]
    congr 1

noncomputable def standardEquiv {N m : Nat} {ok : Nat→Nat→Prop} :
    BridgeRanks N m ok ≃ StandardRanks N m ok :=
  Equiv.ofBijective toStandard toStandard_bijective

end AiresKahnDeletion
#print axioms AiresKahnDeletion.toStandard_bijective
