import KInventoryExact
import NeutralAffineExact

namespace KNeutralExact
open KPhase KProjection KInventoryExact AffineAddress TripTrace
open PhaseProduct (sign)
open IntegerEigen (mat eigvec is_eig nonzero independent)

variable (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ)
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)

def computes (u v : ℤ × ℤ) (neg : Bool) (m : ℤ) (q : ℤ) (hq : q ∈ D) : Bool :=
  let B := bound D f k v
  KNeutralDecider.decidePower closed u v neg m B q hq (bound_zero D f k v)
    (enumArc D f k B v m) (enumVertex D k B) (enumState D k)

theorem computes_correct (u v : ℤ × ℤ) (neg : Bool) (m : ℤ) (q : ℤ) (hq : q ∈ D)
    (A : (ℤ × ℤ) →+ (ℤ × ℤ))
    (aff : ∀ x ∈ D, σ (f x) = A (σ [x]))
    (hu : ∀ p, NeutralTrace.pro u (A p) = sign neg * NeutralTrace.pro u p)
    (hv : ∀ p, NeutralTrace.pro v (A p) = m * NeutralTrace.pro v p)
    (indep : u.1*v.2-u.2*v.1 ≠ 0) (hm : 1 < |m|) :
    computes D f k closed u v neg m q hq = true ↔
      ∃ n, KFactors.Actual (iter f q n) k := by
  have hB := bound_nonneg D f k v
  have safe : bound D f k v ≤ (|m|-1)*bound D f k v := by
    have h : 1 ≤ |m|-1 := by omega
    simpa using mul_le_mul_of_nonneg_right h hB
  exact KNeutralDecider.decidePower_correct closed u v neg m _ q hq _ _ _ _
    (mem_arc D f k _ v m) (mem_vertex D k _) (mem_state D k)
    A aff hu hv indep _ (bound_covers D f k v) hm hB safe

/-- A literal additive power of `k+1` blocks (no condition on the right context). -/
def Contains (w : List ℤ) (k : ℕ) : Prop :=
  ∃ (u r : List ℤ) (B : Fin (k+1) → List ℤ),
    w = u ++ (List.ofFn B).flatten ++ r ∧
    (∀ j, 0 < (B j).length) ∧ (∀ j, σ (B j) = σ (B 0))

theorem remove_right_padding (q : ℤ) (suffix : List ℤ) (hf : f q = q::suffix)
    (grows : ∀ B : ℕ, ∃ n, B < (iter f q n).length) :
    (∃ n, KFactors.Actual (iter f q n) k) ↔ ∃ n, Contains (iter f q n) k := by
  constructor
  · rintro ⟨n,u,r,B,eq,_,pos,same⟩
    exact ⟨n,u,r,B,eq,pos,same⟩
  · rintro ⟨n,u,r,B,eq,pos,same⟩
    have e : iter f q n = u ++ (List.ofFn B).flatten ++ [] ++ r := by simpa using eq
    obtain ⟨l,t,ht,ne⟩ := NeutralFixedPoint.extend_factor f q suffix hf grows n u _ [] r e
    exact ⟨l,u,t,B,by simpa using ht,ne,pos,same⟩

def calculate (a b c d : ℤ) (neg : Bool) (q : ℤ) (hq : q ∈ D) : Bool :=
  let r := sign neg
  let t := NeutralAffineExact.other a d neg
  computes D f k closed (eigvec a b c d r) (eigvec a b c d t) neg t q hq

theorem calculate_correct (a b c d : ℤ) (neg : Bool)
    (aff : ∀ x ∈ D, σ (f x) = mat a b c d (σ [x]))
    (rootEq : (a-sign neg)*(d-sign neg)-b*c=0)
    (expand : 1 < |NeutralAffineExact.other a d neg|)
    (q : ℤ) (hq : q∈D) (suffix : List ℤ) (hf : f q=q::suffix)
    (grows : ∀ B : ℕ, ∃ n, B < (iter f q n).length) :
    calculate D f k closed a b c d neg q hq = true ↔ ∃ n, Contains (iter f q n) k := by
  let r := sign neg
  let t := NeutralAffineExact.other a d neg
  have ht : (a-t)*(d-t)-b*c=0 := by
    change (a-(a+d-sign neg))*(d-(a+d-sign neg))-b*c=0
    linear_combination rootEq
  have neq : r ≠ t := by
    intro eq
    change 1 < |t| at expand
    rw [← eq] at expand
    cases neg <;> simp [r,sign] at expand
  have hn := nonzero a b c d r t neq ht
  have hn' := nonzero a b c d t r (Ne.symm neq) rootEq
  have ha := is_eig a b c d r rootEq
  have hb := is_eig a b c d t ht
  have hi := independent (mat a b c d) _ _ r t neq hn hn' ha hb
  exact (computes_correct D f k closed _ _ neg t q hq (mat a b c d) aff ha hb hi expand).trans
    (remove_right_padding f k q suffix hf grows)

end KNeutralExact

#print axioms KNeutralExact.calculate_correct
