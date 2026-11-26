import Ribbon
import HaarTwoKernel

namespace RibbonTwo
open HaarVoltage HaarVoltageLift
variable {G H : Type*} [Group G] [Group H]

def Label (x y : G) (a b : Bool) (g : G) : Prop :=
  (a=false ∧ b=false ∧ (g=x ∨ g=x⁻¹)) ∨
  (a=true ∧ b=true ∧ (g=y ∨ g=y⁻¹)) ∨
  (a≠b ∧ g=1)

theorem labeled_of_adj (f : G→*H) (x y : G) (a b : Bool×H)
    (adj : Ribbon.Adj (f x) (f y) a b) :
    ∃ g : G, Label x y a.1 b.1 g ∧ b.2=a.2*f g := by
  rcases adj with ⟨al,bl,forward|back⟩ | ⟨ar,br,forward|back⟩ | ⟨different,same⟩
  · exact ⟨x,Or.inl ⟨al,bl,Or.inl rfl⟩,forward.symm⟩
  · exact ⟨x⁻¹,Or.inl ⟨al,bl,Or.inr rfl⟩,by rw [←back,map_inv,mul_inv_cancel_right]⟩
  · exact ⟨y,Or.inr (Or.inl ⟨ar,br,Or.inl rfl⟩),forward.symm⟩
  · exact ⟨y⁻¹,Or.inr (Or.inl ⟨ar,br,Or.inr rfl⟩),by rw [←back,map_inv,mul_inv_cancel_right]⟩
  · exact ⟨1,Or.inr (Or.inr ⟨different,rfl⟩),by rw [map_one,mul_one,same]⟩

theorem adj_of_labeled (x y : G) (a b : Bool×G) (g : G)
    (p : Label x y a.1 b.1 g) (h : b.2=a.2*g) : Ribbon.Adj x y a b := by
  rcases p with ⟨al,bl,rfl|rfl⟩ | ⟨ar,br,rfl|rfl⟩ | ⟨ne,rfl⟩
  · exact Or.inl ⟨al,bl,Or.inl h.symm⟩
  · exact Or.inl ⟨al,bl,Or.inr (by rw [h,inv_mul_cancel_right])⟩
  · exact Or.inr (Or.inl ⟨ar,br,Or.inl h.symm⟩)
  · exact Or.inr (Or.inl ⟨ar,br,Or.inr (by rw [h,inv_mul_cancel_right])⟩)
  · exact Or.inr (Or.inr ⟨ne,by simpa only [mul_one] using h.symm⟩)

theorem lift_labeled (φ : G →* H) (x y : G) {k : ℕ} [NeZero k]
    (B : Fin k → Bool × H) (inj : Function.Injective B)
    (L : Fin k → G) (labels : ∀ i, Label x y (B i).1 (B (i+1)).1 (L i))
    (walk : ∀ i, (B (i+1)).2 = (B i).2 * φ (L i))
    (d : ℕ) (dp : 0 < d) (hd : orderOf (pathVal L k) = d) :
    Ribbon.Cycle x y (k*d) := by
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
  refine ⟨V,vinj,?_⟩
  intro i
  change Ribbon.Adj x y (V i) (V (index N (i.val+1)))
  have ix : index N (i.val+1) = i+1 := by rw [index_succ,val_index]
  rw [ix]
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
  apply adj_of_labeled x y (V i) (V (i+1)) (L (index k i.val))
  · change Label x y (B (index k i.val)).1 (B (index k (i+1).val)).1 (L (index k i.val))
    rw [bindex,index_succ]
    exact labels _
  · change pathVal L (i+1).val = pathVal L i.val * L (index k i.val)
    rw [pre_eq]
    rfl

end RibbonTwo
#print axioms RibbonTwo.lift_labeled
