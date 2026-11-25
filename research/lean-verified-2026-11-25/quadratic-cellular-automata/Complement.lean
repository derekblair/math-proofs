import Local
import Mathlib.Tactic.Positivity
namespace QuadraticCA
def shift (x : Stream) : Stream := fun i => x (i+1)
lemma d_as_shift (x : Stream) : d x = x+shift x := rfl

lemma local_shift {F : Stream → Stream} (h : Local F) (x : Stream) :
    F (shift x) = shift (F x) := by
  obtain ⟨k,f,H⟩ := h
  ext i
  change F (shift x) i = F x (i+1)
  rw [H,H]; congr 1; ext j
  change x (i+j.val+1) = x (i+1+j.val)
  congr 1; omega
lemma local_polar_one {F : Stream → Stream} (h : Local F) :
    Local (fun x => polar F x 1) := by
  obtain ⟨k,f,H⟩ := h
  use k, fun w => f (w+1)+f w+f 1+f 0
  intro x i
  change F (x+1) i + F x i + F 1 i + F 0 i = _
  rw [H,H,H,H]; rfl

lemma d_comm_linear {L : Stream → Stream} (h : Local L)
    (ha : ∀ x y, L (x+y) = L x + L y) (x : Stream) :
    L (d x) = d (L x) := by
  rw [d_as_shift,ha,local_shift h,d_as_shift]
lemma d_iter_comm_linear {L : Stream → Stream} (h : Local L)
    (ha : ∀ x y, L (x+y) = L x + L y) (r : ℕ) (x : Stream) :
    L (d^[r] x) = d^[r] (L x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',d_comm_linear h ha,ih,Function.iterate_succ_apply']
lemma powered_nonzero_iter_one (r : ℕ) (x : Stream)
    (h : d^[r] x = 0) (nz : x ≠ 0) : ∃ j, d^[j] x = 1 := by
  induction r generalizing x with
  | zero => exact (nz h).elim
  | succ r ih =>
    by_cases hd : d x = 0
    · exact ⟨0,(const_zero_or_one hd).resolve_left nz⟩
    · rw [Function.iterate_succ_apply] at h
      obtain ⟨j,hj⟩ := ih (d x) h hd
      exact ⟨j+1,by simpa only [Function.iterate_succ_apply] using hj⟩

lemma nonzero_local_linear_hits_one {L : Stream → Stream} (h : Local L)
    (ha : ∀ x y, L (x+y) = L x + L y) {X : Stream} (nz : L X ≠ 0) :
    ∃ n > 0, ∃ x : Stream, Periodic n x ∧ L x = 1 := by
  obtain ⟨i,hi⟩ : ∃ i, L X i ≠ 0 := by
    by_contra! hn
    exact nz (funext hn)
  obtain ⟨k,f,H⟩ := h
  let v : Fin k → K := fun j => X (i+j.val)
  obtain ⟨e,z,hz,hvz⟩ := ext_period_pw v
  have nz2 : L z ≠ 0 := by
    intro hz0
    have heq : L z 0 = L X i := by
      rw [H,H]; congr 1; ext j
      simpa [v] using hvz j
    exact hi (heq.symm.trans (congrFun hz0 0))
  have hl : Local L := ⟨k,f,H⟩
  have hd := iterate_d_annihilates (force_period hl hz)
  obtain ⟨j,hj⟩ := powered_nonzero_iter_one _ _ hd nz2
  exact ⟨2^e,by positivity,d^[j] z,periodic_iter_d j hz,(d_iter_comm_linear hl ha j z).trans hj⟩

lemma scalar_sub (A B : Stream) (E : A+B=0) : A=B := sum_eq_zero E
lemma complement_comm {F : Stream → Stream} (h : Local F) (hq : Quad F) (hp : Proper F) :
    ∀ x, F (x+1) = F x+1 := by
  have c := constant_outputs h hp
  have lin0 : ∀ x, polar F x 1 = 0 := by
    intro x
    by_contra nz
    obtain ⟨n,hn,z,hz,H⟩ := nonzero_local_linear_hits_one
      (local_polar_one h) (fun a b => hq a b 1) nz
    change F (z+1)+F z+F 1+F 0=1 at H
    rw [add_assoc (F (z+1)+F z), add_comm (F 1) (F 0), c] at H
    have eq := congrArg (· + (1 : Stream)) H
    have eq' : F (z+1) + F z = 0 := by simpa [add_assoc, stream_self] using eq
    have e := hp n hn (z+1) z (periodic_add hz (periodic_one n)) hz (sum_eq_zero eq')
    exact (one_ne_zero (α:=K)) (add_left_cancel (show z 0 + 1 = z 0 + 0 by simpa using congrFun e 0))
  intro x
  have H := lin0 x
  change F (x+1)+F x+F 1+F 0=0 at H
  rw [add_assoc (F (x+1)+F x), add_comm (F 1) (F 0), c, add_assoc] at H
  exact sum_eq_zero H

end QuadraticCA
