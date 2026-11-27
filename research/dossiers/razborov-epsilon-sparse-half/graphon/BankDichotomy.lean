import CountableIsolate
import OneHeavyStrict
import TwoHeavyStrict

open Set
open scoped BigOperators
namespace SparseHalfCountableEndpoint

variable {ι : Type*}

/-- The analytic outside optimum narrows the complete measurable
classification to four explicit alternatives or a strict pivot. -/
theorem bank_dichotomy (p q : ι → ℝ) (θ h : ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 2) (hp : ∀ i, p i ≤ 2) (hq : ∀ i, 0 ≤ q i)
    (hqp : ∀ i, q i ≤ p i) (hs : Summable (fun i => p i+q i))
    (hh : 0 ≤ h) (hmass : (∑' i, (p i+q i))+h=6)
    (obs : 2 ≤ dual p q θ) :
    (h=2 ∧ ∃ j, p j=2 ∧ q j=2 ∧ ∀ k≠j, p k=0 ∧ q k=0) ∨
    (∃ j, 1<q j ∧ 2+h<p j+q j) ∨
    (h=0 ∧ ∃ s : Finset ι,
      ((s.card=3 ∧ (∀ i∈s, p i=1 ∧ q i=1)) ∨
       (s.card=2 ∧ (∀ i∈s, p i=2 ∧ q i=1))) ∧ (∀ i∉s, p i=0 ∧ q i=0)) ∨
    (∃ i j : ι, i≠j ∧ 1<q i ∧ 1<q j ∧ p i≤p j ∧
      h + (∑' k : ↥(({i,j} : Set ι)ᶜ), (p k.val+q k.val))≤2 ∧
      (p j*(4-max (p i+q j) (p j+q i))<2 ∨
       (h=2/3 ∧ p i=3/2 ∧ p j=3/2 ∧ q i=7/6 ∧ q j=7/6 ∧
         (∑' k : ↥(({i,j} : Set ι)ᶜ), (p k.val+q k.val))=0))) := by
  classical
  by_cases hlarge : 2≤h
  · exact Or.inl (large_isolate p q θ h hθ hp hq hqp hs hlarge hmass obs).2
  right
  by_cases hpivot : ∃ j, 1<q j ∧ 2+h<p j+q j
  · exact Or.inl hpivot
  right
  have hpiv (j) (hj : 1<q j) : p j+q j≤2+h := le_of_not_gt (fun hh=>hpivot ⟨j,hj,hh⟩)
  have pn (i) : 0≤p i := (hq i).trans (hqp i)
  have non (i) : 0≤p i+q i := add_nonneg (pn i) (hq i)
  have hθ1 : 1≤θ := by
    have H := small_price_bound p q θ h hθ.1 hq hqp hs hmass
    nlinarith [mul_nonneg hθ.1 hh]
  let s := (finite_threshold (fun j=>p j+q j) hs (show (0:ℝ)<2 from by norm_num)).subset
    (show {j | 1<q j} ⊆ {j | 2≤p j+q j} from fun j hj => by
      change 1<q j at hj
      change 2≤p j+q j
      linarith [hqp j])
  let S := s.toFinset
  have mem (i) : i ∈ S ↔ 1<q i := s.mem_toFinset
  have hs2 : S.card≤2 := by
    by_contra! hn
    have hn0 : S.Nonempty := Finset.card_pos.mp (by omega)
    have hsum := hs.sum_le_tsum S (fun j _=>non j)
    have hlt : (∑ j∈S, (2:ℝ)) < ∑ j∈S,(p j+q j) := by
      apply Finset.sum_lt_sum_of_nonempty hn0
      intro j hj
      exact (show 2<p j+q j by linarith [(mem j).mp hj,hqp j])
    simp only [Finset.sum_const,nsmul_eq_mul] at hlt
    have hr : (3:ℝ)≤(S.card:ℝ) := by exact_mod_cast hn
    linarith
  have sumV : Summable (fun j => q j*min θ (p j)) := by
    apply Summable.of_nonneg_of_le _ _ (hs.mul_left 2)
    · intro j
      exact mul_nonneg (hq j) (le_min hθ.1 (pn j))
    · intro j
      have H := mul_le_mul_of_nonneg_left ((min_le_left θ (p j)).trans hθ.2) (hq j)
      linarith [pn j]
  have splitM := hs.sum_add_tsum_compl (s:=S)
  have splitV := sumV.sum_add_tsum_compl (s:=S)
  have fincases : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases fincases with h0|h1|h2
  · left
    have hq' (i) : 0≤q i ∧ q i≤1 := ⟨hq i,by
      by_contra! H
      have hh := (mem i).mpr H
      rw [Finset.card_eq_zero.mp h0] at hh
      exact Finset.notMem_empty i hh⟩
    obtain ⟨hz,T,ht,ht'⟩ := zero_heavy p q θ h hθ hp hq' hqp hs hh hmass obs
    exact ⟨hz,T,ht.elim (fun H=>Or.inl H.2) (fun H=>Or.inr H.2),ht'⟩
  · exfalso
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp h1
    have hqi : 1<q i := (mem i).mp (by simp [hi])
    let T := (↑S : Set ι)ᶜ
    have hf (j : T) : 0≤q j.val ∧ q j.val≤1 := ⟨hq _,by
      by_contra! he; exact j.property ((mem _).mpr he)⟩
    have hm := hs.subtype (· ∈ T)
    have hlast := one_heavy_strict (fun j:T=>p j.val) (fun j:T=>q j.val)
      (p i) (q i) θ h ⟨hθ1,hθ.2⟩ hqi (hqp i) (hp i) (fun j=>pn _) hf hm
      (by simp only [hi,Finset.sum_singleton] at splitM; linarith)
      (hpiv i hqi) (lt_of_not_ge hlarge)
    unfold dual at obs
    simp only [hi,Finset.sum_singleton] at splitV
    linarith
  · right
    obtain ⟨i,j,hij,hijS⟩ := Finset.card_eq_two.mp h2
    wlog hr : p i≤p j generalizing i j
    · have hS : S={j,i} := by simpa [Finset.pair_comm] using hijS
      exact this j i hij.symm hS (le_of_not_ge hr)
    let T := (↑S : Set ι)ᶜ
    let L := ∑' k : T, (p k.val+q k.val)
    let V := ∑' k : T, (q k.val*min θ (p k.val))
    have hqi : 1<q i := (mem i).mp (by simp [hijS])
    have hqj : 1<q j := (mem j).mp (by simp [hijS])
    have hf (j : T) : 0≤q j.val ∧ q j.val≤1 := ⟨hq _,by
      by_contra! he; exact j.property ((mem _).mpr he)⟩
    have hm := hs.subtype (· ∈ T)
    have hV := light_rebate (fun j:T=>p j.val) (fun j:T=>q j.val) θ L hθ.1
      (fun j=>pn _) hf hm le_rfl
    have ha : h+p i+q i+p j+q j+L=6 := by
      rw [show (∑ x∈S,(p x+q x))=(p i+q i)+(p j+q j) by simp [hijS,hij]] at splitM
      change (p i+q i)+(p j+q j)+L= _ at splitM
      linarith
    have hbad : 2≤q i*min θ (p i)+q j*min θ (p j)+V-θ := by
      rw [show (∑ x∈S,q x*min θ (p x))=q i*min θ (p i)+q j*min θ (p j) by simp [hijS,hij]] at splitV
      change _+V= _ at splitV
      unfold dual at obs
      linarith
    have he := two_heavy_endpoint h (p i) (q i) (p j) (q j) L V θ hθ1 hh
      (tsum_nonneg (fun j:T=>non _)) hqi hqj (hqp i) (hqp j) hr hV ha (hpiv i hqi) (hpiv j hqj) hbad
    refine ⟨i,j,hij,hqi,hqj,hr,?_⟩
    unfold L T at he
    have ht : (↑S : Set ι)=({i,j} : Set ι) := by rw [hijS]; simp
    rw [ht] at he
    exact he

#print axioms bank_dichotomy
end SparseHalfCountableEndpoint
