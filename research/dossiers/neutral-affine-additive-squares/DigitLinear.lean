import IntegerTrace
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace DigitLinear
variable {I J : Type*} [Fintype I]
variable (A : J → I → ℤ)

def eval (x : I → ℕ) : J → ℤ := fun j => ∑ i, A j i * (x i : ℤ)

def low (x : I → ℕ) (i : I) : Bool := decide (x i % 2 = 1)
def val (q : Bool) : ℕ := if q then 1 else 0

theorem low_val (x : I → ℕ) (i : I) : val (low x i) = x i % 2 := by
  by_cases h : x i%2=1
  · simp [low,val,h]
  · have e : x i%2=0 := by omega
    simp [low,val,h,e]

theorem expand (q : I → Bool) (y : I → ℕ) (j : J) :
    eval A (fun i => val (q i)+2*y i) j =
      eval A (val ∘ q) j + 2*eval A y j := by
  unfold eval
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat, Function.comp_apply]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem halves (x : I → ℕ) :
    x=(fun i => val (low x i)+2*(x i/2)) := by
  funext i
  rw [low_val]
  exact (Nat.mod_add_div (x i) 2).symm

def step (x y : J→ℤ) : Prop :=
  ∃ q : I→Bool, ∀ j, x j = eval A (val ∘ q) j + 2*y j

inductive Accept : (J→ℤ) → Prop
  | done : Accept (fun _ => 0)
  | more {p q} : step A p q → Accept q → Accept p

theorem sound (b : J→ℤ) (h : Accept A b) :
    ∃ x : I → ℕ, eval A x=b := by
  induction h with
  | done => exact ⟨fun _ => 0, by ext j; simp [eval]⟩
  | @more p q h hh ih =>
    obtain ⟨x,v⟩ := ih
    obtain ⟨digits,e⟩ := h
    refine ⟨fun i => val (digits i)+2*x i,?_⟩
    funext j
    rw [expand A, v, ← e]

theorem small_complete (n : ℕ) (x : I→ℕ) (q : ∀ i, x i < 2^n) :
    Accept A (eval A x) := by
  induction n generalizing x with
  | zero =>
    have z : eval A x=fun _=>0 := by
      funext j
      apply Finset.sum_eq_zero
      intro i _
      have z := q i
      have h : x i=0 := by simpa using z
      simp [h]
    rw [z]
    exact .done
  | succ n ih =>
    let y (i : I) := x i / 2
    have hy (i : I) : y i<2^n := by
      have hi := q i
      rw [pow_succ] at hi
      dsimp [y]
      omega
    apply Accept.more _ (ih y hy)
    refine ⟨low x,fun j => ?_⟩
    calc
      eval A x j = eval A (fun i=>val (low x i)+2*y i) j :=
        congrArg (fun q => eval A q j) (halves x)
      _ = _ := expand _ _ _ _

theorem complete (b : J→ℤ) (h : ∃ x : I→ℕ, eval A x=b) : Accept A b := by
  obtain ⟨x,rfl⟩ := h
  let n := ∑ i, x i
  apply small_complete A n x
  intro i
  have h : x i ≤ n := Finset.single_le_sum (f:=x) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  exact h.trans_lt (Nat.lt_two_pow_self (n:=n))

def baseBound [Fintype J] (b : J→ℤ) : ℤ :=
  ∑ j, (|b j| + ∑ i, |A j i|)

theorem base_nonneg [Fintype J] (b : J→ℤ) : 0 ≤ baseBound A b := by
  unfold baseBound
  exact Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _)))

theorem base_b [Fintype J] (b : J→ℤ) (j : J) : |b j|≤baseBound A b := by
  have h : |b j| ≤ |b j| + ∑ i, |A j i| := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine h.trans (Finset.single_le_sum (f:=fun j => |b j| + ∑ i, |A j i|) ?_ (Finset.mem_univ j))
  exact fun j _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))

theorem base_digit [Fintype J] (b : J→ℤ) (q : I→Bool) (j : J) :
    |eval A (val ∘ q) j|≤baseBound A b := by
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  have d : (∑ i, |A j i * ((val (q i) : ℕ) : ℤ)|) ≤ ∑ i, |A j i| := by
    apply Finset.sum_le_sum
    intro i hi
    cases h : q i <;> simp [h,val]
  apply d.trans
  have h : (∑ i, |A j i|) ≤ |b j| + ∑ i, |A j i| := le_add_of_nonneg_left (abs_nonneg _)
  refine h.trans (Finset.single_le_sum (f:=fun j => |b j| + ∑ i, |A j i|) ?_ (Finset.mem_univ j))
  exact fun j _ => add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))

theorem carry_stays (B : ℤ) (b q c : ℤ)
    (e : b = c+2*q) (hb : |b|≤B) (hc : |c|≤B) : |q|≤B := by
  rw [abs_le] at hb hc ⊢
  omega

end DigitLinear
#print axioms DigitLinear.sound
#print axioms DigitLinear.complete
#print axioms DigitLinear.base_digit
#print axioms DigitLinear.carry_stays
