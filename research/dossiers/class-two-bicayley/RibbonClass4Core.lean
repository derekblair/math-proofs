import RibbonClass4Data
import RibbonAbelian

namespace RibbonClass4

open HaarClass4Table HaarClass4Normal HaarClass4Projection HaarClass4CollectCore
open RibbonClass4Data

variable {G H : Type*} [Group G] [Group H]

def target (M : Data G) (b : Fin 3) : G :=
  match pick b with
  | .a => M.a
  | .b => M.b
  | .d => M.d

def rootGood (c : H) : Prop := c≠1 ∧ c^2≠1 ∧ c^3≠1

theorem no_small (c : H) (good : rootGood c) (d : ℤ) (s : RibbonClass4Data.small d) : c^d≠1 := by
  obtain ⟨h1,h2,h3⟩ := good
  rcases s with h|h|h|h|h|h <;> subst d <;> norm_num [zpow_neg] <;> assumption

private theorem comm_of_tail_eq (u x t : G) (e : ℤ) (ue : unit e)
    (ct : Commute t x) (h : u^e*t=1) : Commute u x := by
  have F : u^e=t⁻¹ := by calc
    _ = (u^e*t)*t⁻¹ := by group
    _ = _ := by rw [h,one_mul]
  rcases ue with H|H
  · rw [H,zpow_one] at F
    rw [F]
    exact ct.inv_left
  · rw [H,zpow_neg_one] at F
    have Q := congrArg (fun g : G => g⁻¹) F
    simpa using (show Commute (u⁻¹)⁻¹ x from by rw [F]; exact (ct.inv_left).inv_left)

private theorem cancel_corr (u x c : G) (h : u*x=x*u*c) (k : Commute u x) : c=1 := by
  have e : (x*u)*c=(x*u)*1 := by rw [← h,k.eq,mul_one]
  exact mul_left_cancel e

private theorem tail_collision (M : Data G) (sel : Fin 3) (d : Row)
    (hs : target M sel≠1) (h : eval M d=1)
    (hi : d.i=0) (hj : d.j=0) (hc : d.c=0)
    (clash : match pick sel with
       | .a => (unit d.u ∧ d.v=0) ∨ (d.u=0 ∧ d.v=0 ∧ unit d.a ∧ d.b=0 ∧ d.d=0)
       | .b => (unit d.u ∧ d.v=0) ∨ (d.u=0 ∧ d.v=0 ∧ d.a=0 ∧ unit d.b ∧ d.d=0)
       | .d => (d.u=0 ∧ unit d.v) ∨ (d.u=0 ∧ d.v=0 ∧ d.a=0 ∧ d.b=0 ∧ unit d.d)) : False := by
  let t := tail M d.a d.b d.d
  have E : M.u^d.u*M.v^d.v*t=1 := by
    simpa [eval,mid,hi,hj,hc,t] using h
  have unit_reject (g : G) (e : ℤ) (hs : g ≠ 1) (su : unit e) (eq : g^e=1) : False := by
    rcases su with h|h <;> exact hs (by simpa [h] using eq)
  fin_cases sel
  · change M.a≠1 at hs
    change (unit d.u ∧ d.v=0) ∨ _ at clash
    rcases clash with ⟨e,z⟩ | ⟨u,v,e,b,d'⟩
    · apply hs
      refine cancel_corr _ _ _ M.ux (comm_of_tail_eq M.u M.x t d.u e (tail_center M _ _ _ _) ?_)
      simpa [z] using E
    · exact unit_reject _ _ hs e (by simpa [u,v,t,tail,b,d'] using E)
  · change M.b≠1 at hs
    change (unit d.u ∧ d.v=0) ∨ _ at clash
    rcases clash with ⟨e,z⟩ | ⟨u,v,a,e,d'⟩
    · apply hs
      refine cancel_corr _ _ _ M.uy (comm_of_tail_eq M.u M.y t d.u e (tail_center M _ _ _ _) ?_)
      simpa [z] using E
    · exact unit_reject _ _ hs e (by simpa [u,v,t,tail,a,d'] using E)
  · change M.d≠1 at hs
    change (d.u=0 ∧ unit d.v) ∨ _ at clash
    rcases clash with ⟨z,e⟩ | ⟨u,v,a,b,e⟩
    · apply hs
      refine cancel_corr _ _ _ M.vy (comm_of_tail_eq M.v M.y t d.v e (tail_center M _ _ _ _) ?_)
      simpa [z] using E
    · exact unit_reject _ _ hs e (by simpa [u,v,t,tail,a,b] using E)

theorem inject_rows (M : Data G) (φ : G →* H) (k : KillsMid M φ)
    (good : rootGood (φ M.c)) (sel : Fin 3) (hs : target M sel≠1) :
    Function.Injective (fun i : Fin 32 => eval M (P (pick sel) i)) := by
  intro i j eq
  by_contra neq
  let p := P (pick sel) i
  let q := P (pick sel) j
  let d := diff p q
  have E := projections_of_equal M φ k p q eq
  have T := sep sel i j neq
  change admissible (pick sel) d at T
  rcases T with h|h|⟨hi,hj,h⟩|⟨hi,hj,hc,tail⟩
  · exact no_small _ good _ h E.1
  · exact no_small _ good _ h E.2.1
  · exact no_small _ good _ h (E.2.2 hi hj)
  · exact tail_collision M sel d hs (equal_diff M p q hi hj eq) hi hj hc tail

theorem eval_step (M : Data G) (sel : Fin 3) (n : Nat) (hn : n<32) :
    eval M (row (pick sel) (n+1)) = eval M (row (pick sel) n) *
      (if signs (pick sel) n then (if n%2=0 then M.x else M.y)
         else (if n%2=0 then M.x else M.y)⁻¹) := by
  let p := row (pick sel) n
  have R : suitable p.i := range sel ⟨n,hn⟩
  change eval M (step (pick sel) n p) = eval M p * _
  by_cases E : n%2=0 <;> by_cases D : signs (pick sel) n
  · simpa [step,E,D] using eval_x M p
  · have F := eval_x M (leftX p)
    rw [cancelX] at F
    simpa [step,E,D] using (eq_mul_inv_iff_mul_eq.mpr F.symm)
  · simpa [step,E,D] using eval_y M p R
  · have R' : suitable (leftY p).i := R
    have F := eval_y M (leftY p) R'
    rw [cancelY] at F
    simpa [step,E,D] using (eq_mul_inv_iff_mul_eq.mpr F.symm)

end RibbonClass4
#print axioms RibbonClass4.inject_rows
