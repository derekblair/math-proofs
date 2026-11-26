import SemilinearWords
import DigitFinite

namespace SemilinearDecide
open SemilinearWords DigitLinear
variable {J : Type*} [Fintype J] [DecidableEq J]
abbrev Vec (J : Type*) := J→ℤ
variable (S : Finset (Vec J))

def M (j : J) (p : ↥S) : ℤ := p.val j

theorem eval_add (x y : ↥S→ℕ) :
    eval (M S) (fun i => x i+y i) = eval (M S) x + eval (M S) y := by
  funext j
  simp only [eval,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]

theorem eval_start (p : ↥S) :
    eval (M S) (fun i => if i=p then 1 else 0) = p.val := by
  funext j
  unfold eval
  rw [Finset.sum_eq_single p]
  · simp [M]
  · intro x _ ne
    simp [ne]
  · simp

theorem closure_eq_eval (x : Vec J) :
    x ∈ AddSubmonoid.closure (S : Set (Vec J)) ↔ ∃ y : ↥S→ℕ, eval (M S) y=x := by
  constructor
  · intro h
    induction h using AddSubmonoid.closure_induction with
    | mem x h => exact ⟨fun i => if i = ⟨x,h⟩ then 1 else 0,eval_start S ⟨x,h⟩⟩
    | zero => exact ⟨fun _ => 0,by ext j; simp [eval]⟩
    | add x y hx hy ih ih' =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := ih'
      exact ⟨fun i => a i+b i,(eval_add S a b).trans (by rw [ha,hb])⟩
  · rintro ⟨y,rfl⟩
    have hp (p : ↥S) : p.val ∈ AddSubmonoid.closure (S : Set (Vec J)) :=
      AddSubmonoid.subset_closure p.property
    have h : (∑ p : ↥S, y p • p.val) ∈ AddSubmonoid.closure (S : Set (Vec J)) :=
      (AddSubmonoid.closure (S : Set (Vec J))).sum_mem
        (fun p _ => (AddSubmonoid.closure (S : Set (Vec J))).nsmul_mem (hp p) (y p))
    have ee : (∑ p : ↥S, y p • p.val) = eval (M S) y := by
      funext j
      simp [eval,M,Finset.sum_apply,nsmul_eq_mul,mul_comm]
    exact ee ▸ h

def testLin (l : Lin (Vec J)) (w : Vec J) : Bool :=
  DigitFinite.decideCoefficients (M l.p) (w-l.b)

theorem testLin_iff (l : Lin (Vec J)) (w : Vec J) :
    testLin l w = true ↔ w ∈ vec l := by
  rw [testLin,DigitFinite.correct,← closure_eq_eval]
  constructor
  · intro h
    exact ⟨w-l.b,h,by abel⟩
  · rintro ⟨x,h,e⟩
    have r : w-l.b=x := by rw [← e]; abel
    rwa [r]

def test (L : List (Lin (Vec J))) (w : Vec J) : Bool :=
  L.any (fun l => testLin l w)

theorem test_iff (L : List (Lin (Vec J))) (w : Vec J) :
    test L w=true ↔ w∈sem L := by
  simp only [test,List.any_eq_true,testLin_iff,sem,Set.mem_setOf_eq]

end SemilinearDecide

#print axioms SemilinearDecide.closure_eq_eval
#print axioms SemilinearDecide.test_iff
