import Mathlib.Tactic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Nodup

namespace CoverCutoff

variable {α : Type} [DecidableEq α]

/-- An edge is required to go from an earlier to a later vertex. -/
def Good (edge : α→α→Bool) (p : List α) : Prop :=
  p.Pairwise (fun a b => edge b a = false)

lemma good_cons (edge : α→α→Bool) (x : α) (p : List α) :
    Good edge (x::p) ↔ Good edge p ∧ ∀ y∈p, edge y x = false := by
  simp [Good,and_comm]

def minimal (edge : α→α→Bool) (left : List α) (x : α) : Bool :=
  (left.erase x).all (fun y => !(edge y x))

def search (edge : α→α→Bool) : ℕ → List α → List (List α)
  | 0, left => if left.isEmpty then [[]] else []
  | fuel+1, left =>
    (left.filter (minimal edge left)).flatMap fun x =>
      (search edge fuel (left.erase x)).map (List.cons x)

lemma search_mem (edge : α→α→Bool) (fuel : ℕ) (left : List α) (hL : left.Nodup)
    (hlen : left.length=fuel) (p : List α) :
    p ∈ search edge fuel left ↔ p.Perm left ∧ Good edge p := by
  induction fuel generalizing left p with
  | zero =>
    have he : left=[] := List.length_eq_zero_iff.mp hlen
    subst left
    subst_vars; cases p <;> simp [search,Good]
  | succ k ih =>
    have hne : left≠[] := by intro h; simp [h] at hlen
    constructor
    · intro hp
      simp only [search,List.mem_flatMap,List.mem_filter,List.mem_map] at hp
      obtain ⟨x,⟨hxl,hx⟩,q,hq,rfl⟩ := hp
      have hle : (left.erase x).length=k := by rw [List.length_erase_of_mem hxl,hlen]; omega
      obtain ⟨hqm,hqg⟩ := (ih _ (hL.erase x) hle q).1 hq
      refine ⟨(hqm.cons x).trans (List.perm_cons_erase hxl).symm, (good_cons _ _ _).2 ⟨hqg,?_⟩⟩
      intro y hy
      have hy' := hqm.mem_iff.mp hy
      simpa using (List.all_eq_true.mp hx y hy')
    · rintro ⟨hp,hg⟩
      cases p with
      | nil => exact (hne (List.perm_nil.mp hp.symm)).elim
      | cons x q =>
        have hx : x∈left := hp.mem_iff.mp (by simp)
        have hle : (left.erase x).length=k := by rw [List.length_erase_of_mem hx,hlen]; omega
        have hpm : q.Perm (left.erase x) :=
          ((List.perm_cons x).mp (hp.trans (List.perm_cons_erase hx)))
        obtain ⟨hq,hG⟩ := (good_cons _ _ _).mp hg
        have hm : minimal edge left x = true := List.all_eq_true.mpr (by
          intro y hy
          simpa using (hG y (hpm.mem_iff.mpr hy)))
        exact List.mem_flatMap.mpr ⟨x,List.mem_filter.mpr ⟨hx,hm⟩,
          List.mem_map.mpr ⟨q,(ih _ (hL.erase x) hle q).2 ⟨hpm,hq⟩,rfl⟩⟩

lemma search_nodup (edge : α→α→Bool) (fuel : ℕ) (left : List α)
    (hL : left.Nodup) : (search edge fuel left).Nodup := by
  induction fuel generalizing left with
  | zero => simp only [search]; split <;> simp
  | succ k ih =>
    rw [search,List.nodup_flatMap]
    refine ⟨?_,?_⟩
    · intro x hx
      exact (ih _ (hL.erase x)).map (fun _ _ h => (List.cons.inj h).2)
    · apply (hL.filter (minimal edge left)).imp
      intro x y hxy
      change List.Disjoint _ _
      simp only [List.disjoint_left,List.mem_map]
      rintro z ⟨u,hu,rfl⟩ ⟨v,hv,h⟩
      exact hxy (List.cons.inj h).1.symm

end CoverCutoff
