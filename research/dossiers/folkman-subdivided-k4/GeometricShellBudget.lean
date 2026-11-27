import GeometricCutTransfer

namespace RobustFolkman.GeometricGap
open Finset
variable {V : Type*} [DecidableEq V]

/-- No concentration for the full, untrimmed root link is needed:
a first-moment estimate suffices once the tight graph has many edges. -/
theorem shell_loss_expected_bound (P q q' T f ε lost gap : ℝ)
    (P0 : 0≤P) (q0 : 0≤q) (f0 : 0≤f) (f1 : f≤1/2)
    (e0 : 0≤ε) (e1 : ε≤1)
    (hT : (1-f)*T≤P^2*q') (hq : q'≤(1+ε)*q)
    (hl : lost≤f*T) (hg : gap≤P^2*(q'-q)) :
    lost+gap≤(4*f+ε)*P^2*q := by
  have H : T≤4*P^2*q := by
    have a := mul_le_mul_of_nonneg_left hq (sq_nonneg P)
    have b := mul_le_mul_of_nonneg_right (show 1+ε≤(2:ℝ) by linarith only [e1]) q0
    have c := mul_le_mul_of_nonneg_left b (sq_nonneg P)
    have d : P^2*q'≤2*P^2*q := a.trans (c.trans_eq (by ring))
    by_contra! n
    have v : 0≤T := le_trans (by positivity : 0≤4*P^2*q) n.le
    have e := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1-f by linarith only [f1]) v
    linarith only [e,hT,d,n]
  have l := hl.trans (mul_le_mul_of_nonneg_left H f0)
  have dq : q'-q≤ε*q := by nlinarith only [hq]
  have g := hg.trans (mul_le_mul_of_nonneg_left dq (sq_nonneg P))
  nlinarith only [l,g]

theorem shell_budget_cut (H G : EdgeGraph V) (sub : H ⊆ G)
    (M : ℝ) (M0 : 0≤M)
    (large : (9/80:ℝ)*M≤(H.card:ℝ)) (small : (((G\H).card):ℝ)≤M/100)
    (tight : ∀ b : V→Bool, cutCount H b≤(9/16)*(H.card:ℝ)) :
    ∀ b : V→Bool, cutCount G b≤(5/8)*(G.card:ℝ) := by
  refine cut_transfer_one_seventh H G sub ?_ tight
  have h := Finset.card_le_card sub
  rw [Finset.card_sdiff_of_subset sub,Nat.cast_sub h] at small
  linarith only [large,small,M0]

#print axioms shell_loss_expected_bound
#print axioms shell_budget_cut
end RobustFolkman.GeometricGap
