import Orders
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Card

namespace CoverCutoff

def RankOK {n : ℕ} (E : Fin n→Fin n→Bool) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b, E a b = true → p a < p b

lemma good_order_iff {n : ℕ} (E : Fin n→Fin n→Bool) (hir : ∀ a, E a a=false)
    (r : Equiv.Perm (Fin n)) : Good E (List.ofFn r.symm) ↔ RankOK E r := by
  rw [Good,List.pairwise_ofFn]
  constructor
  · intro h a b he
    have hn : a≠b := by intro hab; subst b; simp [hir] at he
    by_contra! hl
    have hh : r b < r a := lt_of_le_of_ne hl (fun hx => hn (r.injective hx.symm))
    have hf := h hh
    simpa [he] using hf
  · intro h i j hij
    by_cases he : E (r.symm j) (r.symm i) = true
    · have hf := h _ _ he
      simp only [Equiv.apply_symm_apply] at hf
      exact (not_lt_of_ge hij.le hf).elim
    · exact Bool.eq_false_iff.mpr he

lemma perm_finRange_of_equiv {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (List.ofFn p).Perm (List.finRange n) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr p.injective) (List.nodup_finRange _)).2
  intro x
  simp [List.mem_ofFn,p.surjective x]

def enumOrders {n : ℕ} (E : Fin n→Fin n→Bool) : List (List (Fin n)) :=
  search E n (List.finRange n)

lemma enum_mem {n : ℕ} (E : Fin n→Fin n→Bool) (l : List (Fin n)) :
    l ∈ enumOrders E ↔ l.Perm (List.finRange n) ∧ Good E l :=
  search_mem E _ _ (List.nodup_finRange _) (by simp) _

lemma enum_nodup {n : ℕ} (E : Fin n→Fin n→Bool) : (enumOrders E).Nodup :=
  search_nodup E _ _ (List.nodup_finRange _)

def enumMap {n : ℕ} (E : Fin n→Fin n→Bool) (hir : ∀ a, E a a=false) :
    {r : Equiv.Perm (Fin n) // RankOK E r} → {l // l ∈ enumOrders E} :=
  fun r => ⟨List.ofFn r.1.symm,(enum_mem E _).mpr
    ⟨perm_finRange_of_equiv r.1.symm,(good_order_iff E hir r.1).mpr r.2⟩⟩

lemma enum_bijective {n : ℕ} (E : Fin n→Fin n→Bool) (hir : ∀ a, E a a=false) :
    Function.Bijective (enumMap E hir) := by
  constructor
  · intro a b h
    have he : (List.ofFn (a.val.symm : Fin n→Fin n)) = List.ofFn (b.val.symm : Fin n→Fin n) :=
      congrArg Subtype.val h
    have he' := List.ofFn_inj.mp he
    apply Subtype.ext
    have hs : a.val.symm = b.val.symm := Equiv.ext (fun i => congrFun he' i)
    exact Equiv.symm_symm a.val ▸ Equiv.symm_symm b.val ▸ congrArg Equiv.symm hs
  · rintro ⟨l,hl⟩
    obtain ⟨hp,hgood⟩ := (enum_mem E _).mp hl
    have hlen : l.length = n := by simpa using hp.length_eq
    have hn := hp.nodup_iff.mpr (List.nodup_finRange _)
    have hmem : ∀ a : Fin n, a∈l := fun a => hp.mem_iff.mpr (List.mem_finRange a)
    let e : Equiv.Perm (Fin n) := (finCongr hlen.symm).trans (hn.getEquivOfForallMemList l hmem)
    have he : List.ofFn (e : Fin n→Fin n) = l := by
      apply List.ext_get
      · simpa using hlen.symm
      · intro i h1 h2
        rw [List.get_ofFn]
        rfl
    have hok : RankOK E e.symm := (good_order_iff E hir e.symm).mp (by simpa only [Equiv.symm_symm,he])
    refine ⟨⟨e.symm,hok⟩,Subtype.ext ?_⟩
    exact he

theorem rank_count {n : ℕ} (E : Fin n→Fin n→Bool) (hir : ∀ a, E a a=false) :
    Nat.card {r : Equiv.Perm (Fin n) // RankOK E r} = (enumOrders E).length := by
  classical
  rw [Nat.card_congr (Equiv.ofBijective (enumMap E hir) (enum_bijective E hir))]
  exact Nat.card_congr ((enum_nodup E).getEquiv (enumOrders E)).symm |>.trans (Nat.card_fin _)

def countSearch {α : Type} [DecidableEq α] (E : α→α→Bool) : ℕ → List α → ℕ
  | 0, left => if left.isEmpty then 1 else 0
  | k+1, left =>
      ((left.filter (minimal E left)).map (fun x => countSearch E k (left.erase x))).sum

lemma countSearch_eq {α : Type} [DecidableEq α] (E : α→α→Bool) (k : ℕ) (left : List α) :
    countSearch E k left = (search E k left).length := by
  induction k generalizing left with
  | zero => simp only [countSearch,search]; split <;> rfl
  | succ k ih =>
    simp only [countSearch,search,List.length_flatMap,List.length_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ih _

#print axioms rank_count
end CoverCutoff
