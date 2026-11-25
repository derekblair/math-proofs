import Obstruction

namespace QuadraticCA

open scoped BigOperators

def coefficient {k : ℕ} (q : Fin k × Fin k → K) (p : Fin k × Fin k) : K :=
    if p.1 < p.2 then q p else 0

def anf {k : ℕ} (c : K) (a : Fin k → K) (q : Fin k × Fin k → K) (v : Fin k → K) : K :=
    c + (∑ i, a i * v i) + ∑ p, coefficient q p * (v p.1 * v p.2)

def explicitPolar {k : ℕ} (q : Fin k × Fin k → K) (v w : Fin k → K) : K :=
    ∑ p, coefficient q p * (v p.1 * w p.2 + w p.1 * v p.2)

lemma polar_anf {k : ℕ} (c : K) (a : Fin k → K) (q : Fin k × Fin k → K) (v w : Fin k → K) :
    localPolar (anf c a q) v w = explicitPolar q v w := by
  unfold localPolar anf explicitPolar
  simp only [Pi.add_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have l : (∑ i, a i * (v i + w i)) = (∑ i, a i * v i) + ∑ i, a i * w i := by
    simp only [mul_add,Finset.sum_add_distrib]
  have r : (∑ p : Fin k × Fin k, coefficient q p * ((v p.1 + w p.1) * (v p.2 + w p.2))) =
      (∑ p : Fin k × Fin k, coefficient q p * (v p.1 * v p.2)) +
      (∑ p : Fin k × Fin k, coefficient q p * (w p.1 * w p.2)) +
      (∑ p : Fin k × Fin k, coefficient q p * (v p.1 * w p.2 + w p.1 * v p.2)) := by
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [l,r]
  generalize (∑ x, a x * v x)=s
  generalize (∑ x, a x * w x)=t
  generalize (∑ p : Fin k × Fin k, coefficient q p * (v p.1 * v p.2))=h
  generalize (∑ p : Fin k × Fin k, coefficient q p * (w p.1 * w p.2))=j
  generalize (∑ p : Fin k × Fin k, coefficient q p * (v p.1 * w p.2 + w p.1 * v p.2))=u
  calc _ = (c+c)+(c+c)+(s+s)+(t+t)+(h+h)+(j+j)+u := by abel
       _ = u := by simp [self_add]

lemma quad_anf {k : ℕ} (c : K) (a : Fin k → K) (q : Fin k × Fin k → K) :
    Quad (localCA (anf c a q)) := by
  intro x y z
  ext i
  change polar (localCA (anf c a q)) (x+y) z i =
      polar (localCA (anf c a q)) x z i + polar (localCA (anf c a q)) y z i
  simp only [polar_localCA,polar_anf,explicitPolar,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

def pulse {k : ℕ} (i : Fin k) : Fin k → K := fun u => if u=i then 1 else 0

lemma pulse_detect {k : ℕ} (q : Fin k × Fin k → K) (i j : Fin k) (hij : i<j) :
    explicitPolar q (pulse i) (pulse j) = q (i,j) := by
  unfold explicitPolar
  rw [Finset.sum_eq_single (i,j)]
  · simp [coefficient,pulse,hij,ne_of_lt hij,ne_of_gt hij]
  · intro p _ hp
    rcases p with ⟨u,v⟩
    by_cases hu : u=i
    · subst u
      have hv : v ≠ j := fun h => hp (by rw [h])
      simp [pulse, hv, ne_of_lt hij]
    · by_cases huj : u=j
      · subst u
        by_cases hvi : v=i
        · subst v
          simp [coefficient, not_lt_of_ge hij.le]
        · simp [pulse,hu,hvi]
      · simp [pulse,hu,huj]
  · simp

/-- The exact finite-ring formulation. Any quadratic ANF term of a binary proper
lifting is zero, with no restriction on the diameter. -/
theorem proper_lifting_no_quadratic {k : ℕ} (c : K) (a : Fin k → K)
    (q : Fin k × Fin k → K)
    (h : ∀ n, k ≤ n → Function.Bijective (@ringLift k n (anf c a q))) :
    ∀ i j : Fin k, i<j → q (i,j)=0 := by
  intro i j hij
  have p := no_nonzero_polar (anf c a q) (quad_anf c a q)
    (proper_of_finite (anf c a q) fun n hn => (h n hn).1) (pulse i) (pulse j)
  rw [polar_anf, pulse_detect q i j hij] at p
  exact p

/-- There does not exist a proper lifting of algebraic degree two. -/
theorem no_degree_two_proper_lifting :
    ¬ ∃ (k : ℕ) (c : K) (a : Fin k → K) (q : Fin k × Fin k → K),
      (∃ i j : Fin k, i<j ∧ q (i,j) ≠ 0) ∧
        ∀ n, k ≤ n → Function.Bijective (@ringLift k n (anf c a q)) := by
  intro E
  obtain ⟨k,c,a,q,⟨i,j,hij,hneq⟩,h⟩ := E
  exact hneq (proper_lifting_no_quadratic c a q h i j hij)

#print axioms no_degree_two_proper_lifting
end QuadraticCA
