import HaarDerivedHaarTransfer
import HaarDerivedWreathAllFlow

namespace HaarDerivedWreathGirth
open HaarDerivedWreathCore HaarDerivedWreathTrace HaarDerivedHaarTransfer
open HaarDerivedCoverTransfer HaarDerivedModThree
open HaarCycle HaarAllNoncommuting
open HaarHalfCollision (branch symmetric port)
open HaarSharpPortGeometry (oriented)
variable {Q : Type*} [Group Q] [DecidableEq Q]

theorem basePort_inj (x y : Q) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    Function.Injective (basePort x y) :=
  HaarReducedWalkCycle.port_inj x y hx hy hxy

theorem step_inj (x y : Q) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (a : Bool × Q) : Function.Injective (step x y a) := by
  intro c d e
  have eq := congrArg (fun t : Bool × Q => t.2) e
  have H : oriented (basePort x y) a.1 c=oriented (basePort x y) a.1 d := mul_left_cancel eq
  apply basePort_inj x y hx hy hxy
  cases b : a.1
  · simpa [oriented,b] using H
  · exact inv_injective (by simpa [oriented,b] using H)

theorem step_reverse (x y : Q) (a : Bool × Q) (j : Fin 3) :
    step x y (step x y a j) j=a := by
  rcases a with ⟨s,g⟩
  cases s <;> simp [step,oriented,mul_assoc]

theorem edgeFlow_indicator (x y : Q) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (r : Q) (j : Fin 3) (nj : j≠0) (a : Bool × Q) (c : Fin 3) :
    let low := (false,r)
    let high := step x y low j
    edgeFlow x y a c (decide (j=2)) r =
      (if a=low ∧ step x y a c=high then 1 else 0) -
      (if a=high ∧ step x y a c=low then 1 else 0) := by
  dsimp
  have classTag : (c=0 ∨ (c=2) ≠ decide (j=2)) ↔ c≠j := by
    fin_cases j <;> fin_cases c <;> simp_all
  simp only [edgeFlow,classTag]
  by_cases C : c=j
  · subst c
    rcases a with ⟨s,g⟩
    rw [if_neg (fun h => h rfl)]
    cases s
    · have good : ((false,g)=(false,r) ∧
          step x y (false,g) j=step x y (false,r) j) ↔ g=r := by
        constructor
        · exact fun E => congrArg Prod.snd E.1
        · rintro rfl
          exact ⟨rfl,rfl⟩
      have no : ¬ ((false,g)=step x y (false,r) j ∧ step x y (false,g) j=(false,r)) := by
        intro E
        exact Bool.noConfusion (congrArg Prod.fst E.1)
      simp only [if_neg no,good]
      change (if g=r then (1:ℤ) else 0) = (if g=r then 1 else 0)-0
      rw [sub_zero]
    · have good : ((true,g)=step x y (false,r) j ∧ step x y (true,g) j=(false,r)) ↔
          (step x y (true,g) j).2=r := by
        constructor
        · exact fun e => congrArg Prod.snd e.2
        · intro e
          have eq : step x y (true,g) j=(false,r) := Prod.ext rfl e
          have rev := step_reverse x y (true,g) j
          exact ⟨rev.symm.trans (congrArg (fun p => step x y p j) eq),eq⟩
      have none : ¬ ((true,g)=(false,r) ∧ step x y (true,g) j=step x y (false,r) j) := by
        intro E
        exact Bool.noConfusion (congrArg Prod.fst E.1)
      simp only [if_neg none,good]
      change (if (step x y (true,g) j).2=r then (-1:ℤ) else 0) =
        0-(if (step x y (true,g) j).2=r then 1 else 0)
      by_cases h : (step x y (true,g) j).2=r <;> simp [h]
  · have noForward : ¬(a=(false,r) ∧ step x y a c=step x y (false,r) j) := by
      rintro ⟨rfl,E⟩
      exact C (step_inj x y hx hy hxy _ E)
    have noBack : ¬(a=step x y (false,r) j ∧ step x y a c=(false,r)) := by
      intro ⟨H,E⟩
      have q := step_reverse x y (false,r) j
      rw [←H] at q
      exact C (step_inj x y hx hy hxy _ (E.trans q.symm))
    simp [C,noForward,noBack]

theorem top_edge (x y : Q) {u v : Bool × W Q}
    (e : haarAdj (liftPort x y 1) (liftPort x y 2) u v) :
    ∃ c, topStep x y u c=v := by
  obtain ⟨S,c,H⟩ := branch (liftPort x y 1) (liftPort x y 2) u v e
  refine ⟨c,Prod.ext S.symm ?_⟩
  change u.2 * oriented (liftPort x y) u.1 c=v.2
  have j : port (liftPort x y 1) (liftPort x y 2) c=liftPort x y c := by
    fin_cases c <;> rfl
  rw [H,j]
  rfl

end HaarDerivedWreathGirth
