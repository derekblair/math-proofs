import IntegerEigen

namespace NeutralAffineExact
open IntegerEigen NeutralFixedPoint NeutralDecider PhaseProduct AffineAddress TripTrace

def other (a d : ℤ) (neg : Bool) : ℤ := a+d-sign neg

def calculate (D : Finset ℤ) (f : ℤ → List ℤ)
    (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    (a b c d : ℤ) (neg : Bool) (q : ℤ) (hq : q ∈ D) : Bool :=
  let r := sign neg
  let t := other a d neg
  decides D f closed (eigvec a b c d r) (eigvec a b c d t) t neg q hq

theorem calculate_correct (D : Finset ℤ) (f : ℤ → List ℤ)
    (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
    (a b c d : ℤ) (neg : Bool)
    (aff : ∀ x ∈ D, σ (f x) = mat a b c d (σ [x]))
    (rootEq : (a-sign neg)*(d-sign neg)-b*c=0)
    (expand : 1 < |other a d neg|)
    (q : ℤ) (hq : q∈D) (suffix : List ℤ) (prolong : f q=q::suffix)
    (grows : ∀ B : ℕ, ∃ n, B < (iter f q n).length) :
    calculate D f closed a b c d neg q hq = true ↔
    ∃ (n : ℕ) (x y z t : List ℤ), iter f q n = x++y++z++t ∧
      0 < y.length ∧ y.length=z.length ∧ y.sum=z.sum := by
  let r := sign neg
  let t := other a d neg
  have ht : (a-t)*(d-t)-b*c=0 := by
    change (a-(a+d-sign neg))*(d-(a+d-sign neg))-b*c=0
    linear_combination rootEq
  have neq : r≠t := by
    intro eq
    change 1 < |t| at expand
    rw [← eq] at expand
    cases neg <;> simp [r,sign] at expand
  have hn := nonzero a b c d r t neq ht
  have hn' := nonzero a b c d t r (Ne.symm neq) rootEq
  have ha := is_eig a b c d r rootEq
  have hb := is_eig a b c d t ht
  have hi := independent (mat a b c d) _ _ r t neq hn hn' ha hb
  exact decides_all_factors D f closed (mat a b c d) aff _ _ t neg q hq ha hb expand hi
    suffix prolong grows

end NeutralAffineExact

#print axioms NeutralAffineExact.calculate_correct
