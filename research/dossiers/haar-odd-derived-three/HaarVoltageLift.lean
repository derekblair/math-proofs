import HaarVoltage

namespace HaarVoltageLift
open HaarCycle HaarAllNoncommuting HaarVoltage

variable {G H : Type*} [Group G] [Group H]

theorem val_index {n : ℕ} [NeZero n] (i : Fin n) : index n i.val = i :=
  Fin.ext (index_lt n i.isLt)

theorem lift_labeled (φ : G →* H) (x y : G) {k : ℕ} [NeZero k]
    (B : Fin k → Bool × H) (inj : Function.Injective B)
    (s : Fin k → G) (labels : ∀ i, withLabel x y (s i))
    (flip : ∀ i, (B i).1 ≠ (B (i+1)).1)
    (walk : ∀ i, (B (i+1)).2 = (B i).2 * φ (stepLabel (B i).1 (s i)))
    (d : ℕ) (dp : 0 < d) (hd : orderOf (pathVal (fun i => stepLabel (B i).1 (s i)) k) = d) :
    HasCycle x y (k*d) := by
  let L : Fin k → G := fun i => stepLabel (B i).1 (s i)
  let g := pathVal L k
  let N := k*d
  have kp : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have np : 0 < N := Nat.mul_pos kp dp
  let : NeZero N := ⟨Nat.ne_of_gt np⟩
  change orderOf g = d at hd
  have end_one : pathVal L N = 1 := by
    change pathVal L (k*d) = 1
    rw [Nat.mul_comm k d, ← Nat.add_zero (d*k),prefix_blocks]
    change g^d * 1 = 1
    rw [mul_one, ← hd, pow_orderOf_eq_one]
  let V : Fin N → Bool × G := fun i => ((B (index k i.val)).1, pathVal L i.val)
  have vinj : Function.Injective V := by
    intro i j e
    have el : (B (index k i.val)).1 = (B (index k j.val)).1 := congrArg (fun w : Bool × G => w.1) e
    have er : pathVal L i.val = pathVal L j.val := congrArg (fun w : Bool × G => w.2) e
    have ei : index k i.val = index k j.val := by
      apply inj
      refine Prod.ext el ?_
      rw [← prefix_project φ B L walk i.val, ← prefix_project φ B L walk j.val,er]
    have r : i.val%k = j.val%k := congrArg Fin.val ei
    have ep : g^(i.val/k) = g^(j.val/k) := by
      have Ii := Nat.div_add_mod i.val k
      have Ij := Nat.div_add_mod j.val k
      rw [Nat.mul_comm] at Ii Ij
      rw [← Ii, ← Ij, prefix_blocks, prefix_blocks,r] at er
      exact mul_right_cancel er
    have bi : i.val/k < orderOf g := by
      rw [hd,Nat.div_lt_iff_lt_mul kp,Nat.mul_comm]; exact i.isLt
    have bj : j.val/k < orderOf g := by
      rw [hd,Nat.div_lt_iff_lt_mul kp,Nat.mul_comm]; exact j.isLt
    have eq := pow_injOn_Iio_orderOf bi bj ep
    apply Fin.ext
    rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod j.val k, eq,r]
  refine cycle_form V vinj ?_
  intro i
  have ix : index N (i.val+1) = i+1 := by rw [index_succ,val_index]
  have bindex : index k (i+1).val = index k (i.val+1) := by
    rw [← ix]
    apply Fin.ext
    change ((i.val+1)%N)%k = (i.val+1)%k
    exact Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right k d)
  have pre_eq : pathVal L (i+1).val = pathVal L (i.val+1) := by
    rw [← ix]
    change pathVal L ((i.val+1)%N) = pathVal L (i.val+1)
    by_cases lt : i.val+1 < N
    · rw [Nat.mod_eq_of_lt lt]
    · have z : i.val+1=N := by have ii := i.isLt; omega
      rw [z,Nat.mod_self,end_one]
      rfl
  apply adj_of_labeled x y (V i) (V (i+1)) (s (index k i.val)) (labels _)
  · change (B (index k i.val)).1 ≠ (B (index k (i+1).val)).1
    rw [bindex,index_succ]
    exact flip _
  · change pathVal L (i+1).val = pathVal L i.val * stepLabel (B (index k i.val)).1 (s (index k i.val))
    rw [pre_eq]
    rfl

end HaarVoltageLift

#print axioms HaarVoltageLift.lift_labeled
