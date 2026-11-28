import RamseySearch
import Mathlib.Algebra.Group.Fin.Basic

namespace Erdos151Ramsey.Seed64
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

def diffMask : Nat :=
  (2^3+2^4+2^9+2^15+2^17+2^25+2^38+2^46+2^48+2^54+2^59+2^60)

def adj (a b : Fin 63) : Bool := diffMask.testBit (b-a).val

def graph (a b : Fin 63) : Prop := adj a b = true

theorem adj_shift (x y a : Fin 63) : adj (x-a) (y-a) = adj x y := by
  unfold adj
  rw [sub_sub_sub_cancel_right]

def shift (a : Fin 63) : Fin 63 ↪ Fin 63 where
  toFun x := x-a
  inj' u v h := by
    change u-a = v-a at h
    have eq := congrArg (fun t : Fin 63 => t+a) h
    simpa only [sub_add_cancel] using eq

@[simp] theorem shift_apply (a x : Fin 63) : shift a x = x-a := rfl

theorem rooted_bound
    (checked : ∀ T : Finset (Fin 63), (∀ v ∈ T, v ≠ 0 ∧ ¬ graph 0 v) →
      Independent graph T → T.card < 13)
    (S : Finset (Fin 63)) (ind : Independent graph S) : S.card ≤ 13 := by
  suffices H : 13 < S.card → False from Nat.le_of_not_gt H
  intro too
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  let T := (S.map (shift a)).erase 0
  have zero_mem : (0 : Fin 63) ∈ S.map (shift a) := by
    apply Finset.mem_map.mpr
    exact ⟨a,ha, (shift_apply a a).trans (sub_self a)⟩
  have bound : 13 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_erase_of_mem zero_mem, Finset.card_map]
    omega
  have hind : Independent graph T := by
    intro u hu v hv hadj
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hu)
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hv)
    apply ind x hx y hy
    change adj (shift a x) (shift a y) = true at hadj
    change adj x y = true
    simpa only [shift_apply, adj_shift] using hadj
  have mem : ∀ v ∈ T, v ≠ 0 ∧ ¬ graph 0 v := by
    intro v hv
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
    refine ⟨hne,?_⟩
    rw [shift_apply]
    change adj 0 (x-a) ≠ true
    have h := adj_shift a x a
    rw [sub_self] at h
    rw [h]
    exact ind a ha x hx
  exact (Nat.not_lt_of_ge bound) (checked T mem hind)

theorem graph_irrefl : ∀ a : Fin 63, ¬ graph a a := by
  intro a
  change diffMask.testBit (a-a).val ≠ true
  rw [sub_self]
  decide

theorem triangle_rooted
    (checked : ∀ b c : Fin 63, graph 0 b → graph b c → ¬ graph 0 c) :
    TriangleFree graph := by
  intro a b c ab bc ac
  have tr : ∀ x y : Fin 63, graph (x-a) (y-a) ↔ graph x y := by
    intro x y
    exact Iff.of_eq (congrArg (fun b : Bool => b = true) (adj_shift x y a))
  exact checked (b-a) (c-a) (by simpa only [sub_self] using (tr a b).mpr ab)
    ((tr b c).mpr bc) (by simpa only [sub_self] using (tr a c).mpr ac)
end Erdos151Ramsey.Seed64
