import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
namespace QuadraticCA
abbrev K := ZMod 2
abbrev Stream := ℕ → K
def d (x : Stream) : Stream := fun i => x i + x (i + 1)
def Periodic (n : ℕ) (x : Stream) : Prop := ∀ i, x (i+n) = x i
def EventuallyZero (x : Stream) : Prop := ∃ n, ∀ i ≥ n, x i = 0
lemma self_add (a : K) : a + a = 0 := by
  have h : (2 : K) = 0 := by decide
  calc a + a = 2 * a := by ring
       _ = 0 := by rw [h, zero_mul]
lemma add_eq_zero_iff (a b : K) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have e := congrArg (· + b) h
    simpa [add_assoc, self_add] using e
  · rintro rfl; exact self_add _
lemma d_add (x y : Stream) : d (x+y) = d x + d y := by
  ext i
  change (x i+y i) + (x (i+1)+y (i+1)) = (x i+x (i+1))+(y i+y (i+1))
  abel
lemma d_zero : d 0 = 0 := by ext i; simp [d]
lemma d_one : d 1 = 0 := by ext i; exact self_add 1
lemma periodic_d {n : ℕ} {x : Stream} (h : Periodic n x) : Periodic n (d x) := by
  intro i
  simp only [d]
  rw [show i+n+1 = i+1+n by omega, h i, h (i+1)]
lemma periodic_iter_d (r : ℕ) {n : ℕ} {x : Stream} (h : Periodic n x) : Periodic n (d^[r] x) := by
  induction r with
  | zero => exact h
  | succ r ih => rw [Function.iterate_succ_apply']; exact periodic_d ih
lemma iterate_d_pow (e : ℕ) (x : Stream) (i : ℕ) :
    (d^[2^e] x) i = x i + x (i+2^e) := by
  induction e generalizing x i with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ, Nat.mul_two, Function.iterate_add_apply, ih, ih, ih]
    rw [show i + 2^e + 2^e = i + (2^e + 2^e) by omega]
    calc (x i + x (i + 2^e)) + (x (i + 2^e) + x (i + (2^e + 2^e))) =
          x i + (x (i + 2^e) + x (i + 2^e)) + x (i + (2^e + 2^e)) := by abel
         _ = _ := by rw [self_add, add_zero]
lemma iterate_d_annihilates {e : ℕ} {x : Stream} (h : Periodic (2^e) x) :
    d^[2^e] x = 0 := by ext i; rw [iterate_d_pow, h]; exact self_add _
lemma d_const {x : Stream} (h : d x = 0) (i : ℕ) : x i = x 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : x i + x (i+1) = 0 := congrFun h i
    exact ((add_eq_zero_iff _ _).1 hi).symm.trans ih
lemma d_eventual {x : Stream} (h : EventuallyZero x) : EventuallyZero (d x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun i hi => by simp [d, hn i hi, hn (i+1) (by omega)]⟩
lemma eventual_d_zero {x : Stream} (ex : EventuallyZero x) (dx : d x = 0) : x = 0 := by
  obtain ⟨n, hn⟩ := ex
  ext i
  exact (d_const dx i).trans ((d_const dx n).symm.trans (hn n le_rfl))
lemma const_zero_or_one {x : Stream} (h : d x = 0) : x = 0 ∨ x = 1 := by
  have H : ∀ a : K, a = 0 ∨ a = 1 := by decide
  rcases H (x 0) with h0 | h1
  · exact Or.inl (funext fun i => (d_const h i).trans h0)
  · exact Or.inr (funext fun i => (d_const h i).trans h1)
end QuadraticCA
