import Chain
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace ZFChain
open Finset
@[simp] theorem blk_left {n} (e : Fin (n+1)) : blk (left e) = e.castSucc := rfl
@[simp] theorem blk_right {n} (e : Fin (n+1)) : blk (right e) = e.succ := rfl
@[simp] theorem wire_left {n} (e : Fin (n+1)) : wire (left e) = out e.castSucc := rfl
@[simp] theorem wire_right {n} (e : Fin (n+1)) : wire (right e) = 6 := rfl

theorem left_inj {n} : Function.Injective (@left n) := by
  intro a b h
  have h' := congrArg (fun (x : V n) => (blk x).val) h
  exact Fin.ext h'
theorem right_inj {n} : Function.Injective (@right n) := by
  intro a b h
  have h' := congrArg (fun (x : V n) => (blk x).val) h
  exact Fin.ext (Nat.succ.inj h')
theorem left_ne_right {n} (a b : Fin (n+1)) : left a ≠ right b := by
  intro h
  have h' := congrArg (fun (x : V n) => (blk x).val) h
  simp only [blk_left,blk_right,Fin.val_castSucc,Fin.val_succ] at h'
  have hm : mid a.castSucc = true := by
    unfold mid
    simp only [decide_eq_true_eq,Fin.val_castSucc]
    omega
  have hw := congrArg wire h
  simp [out,hm] at hw

theorem cross_left {n} (e : Fin (n+1)) (x : V n) :
    Cross (left e) x ↔ x = right e := by
  constructor
  · rintro ⟨f,⟨h,rfl⟩|⟨h,_⟩⟩
    · rw [left_inj h]
    · exact (left_ne_right _ _ h).elim
  · rintro rfl
    exact ⟨e,Or.inl ⟨rfl,rfl⟩⟩

theorem cross_right {n} (e : Fin (n+1)) (x : V n) :
    Cross (right e) x ↔ x = left e := by
  constructor
  · rintro ⟨f,⟨h,_⟩|⟨h,rfl⟩⟩
    · exact (left_ne_right _ _ h.symm).elim
    · rw [right_inj h]
  · rintro rfl
    exact ⟨e,Or.inr ⟨rfl,rfl⟩⟩

theorem core_not_cross {n} {x y : V n} (h : (wire x).val < 6) : ¬ Cross x y := by
  rintro ⟨e,⟨rfl,_⟩|⟨rfl,_⟩⟩
  · simp only [wire_left,out] at h
    split at h <;> norm_num at h
  · norm_num at h

theorem port_is_bridge {n} (x : V n) (h : 6 ≤ (wire x).val) :
    ∃ e : Fin (n+1), x = left e ∨ x = right e := by
  have hh := (wire x).isLt
  have hi := (blk x).isLt
  by_cases ha : (wire x).val = 6
  · by_cases hb : (blk x).val = 0
    · let e : Fin (n+1) := ⟨0,by omega⟩
      have hmid : mid e.castSucc = false := by simp [mid,e]
      exact ⟨e,Or.inl (vertex_ext (Fin.ext hb) (Fin.ext (by simpa [out,hmid] using ha)))⟩
    · let e : Fin (n+1) := ⟨(blk x).val - 1,by omega⟩
      exact ⟨e,Or.inr (vertex_ext (Fin.ext (by simp [e]; omega)) (Fin.ext ha))⟩
  · have hb : (wire x).val = 7 := by omega
    have hm : mid (blk x) = true := by
      have hh : legal (mid (blk x)) (wire x) := x.property
      exact hh.resolve_right (by omega)
    have he : (blk x).val < n+1 := by simp [mid] at hm; omega
    let e : Fin (n+1) := ⟨(blk x).val,he⟩
    have hblk : blk x = e.castSucc := Fin.ext rfl
    exact ⟨e,Or.inl (vertex_ext hblk (Fin.ext (by simpa [out,← hblk,hm] using hb)))⟩

theorem cross_port_unique {n} (x : V n) (h : 6 ≤ (wire x).val) :
    ∃ y, Cross x y ∧ ∀ z, Cross x z → z = y := by
  obtain ⟨e,rfl|rfl⟩ := port_is_bridge x h
  · exact ⟨right e,(cross_left _ _).mpr rfl,fun z hz => (cross_left _ _).mp hz⟩
  · exact ⟨left e,(cross_right _ _).mpr rfl,fun z hz => (cross_right _ _).mp hz⟩

theorem graph_triangleFree {n} (x y z : V n) (hxy : adj x y) (hyz : adj y z) :
    ¬ adj z x := by
  intro hzx
  have no_two (a b c : V n) (hab : Cross b a) (hbc : Cross b c) (hac : adj c a) : False := by
    have hp : 6 ≤ (wire b).val := by
      by_contra hu
      exact core_not_cross (by omega) hab
    obtain ⟨_,_,hu⟩ := cross_port_unique b hp
    exact adj_irrefl _ ((hu _ hbc |>.trans (hu _ hab).symm) ▸ hac)
  have cross_symm {a b : V n} (h : Cross a b) : Cross b a := by
    rcases h with ⟨e,⟨h,q⟩|⟨h,q⟩⟩
    · exact ⟨e,Or.inr ⟨q,h⟩⟩
    · exact ⟨e,Or.inl ⟨q,h⟩⟩
  rcases hxy with ⟨ha,he⟩|hb <;> rcases hyz with ⟨hc,hf⟩|hd <;> rcases hzx with ⟨hg,hi⟩|hj
  · rw [← ha] at hf
    rw [hg] at hi
    rw [loc_no_triangle _ _ _ _ he hf] at hi
    contradiction
  · exact cross_ne hj (ha.trans hc).symm
  · exact cross_ne hd (hg.trans ha).symm
  · exact no_two y z x (cross_symm hd) hj (Or.inl ⟨ha,he⟩)
  · exact cross_ne hb (hc.trans hg).symm
  · exact no_two z x y (cross_symm hj) hb (Or.inl ⟨hc,hf⟩)
  · exact no_two x y z (cross_symm hb) hd (Or.inl ⟨hg,hi⟩)
  · exact no_two x y z (cross_symm hb) hd (Or.inr hj)

end ZFChain
