import NeutralDecider

namespace NeutralFixedPoint
open TripTrace AffineAddress NeutralDecider PhaseProduct

theorem iter_prefix (f : ℤ → List ℤ) (a : ℤ) (v : List ℤ) (hf : f a = a::v)
    (n : ℕ) : iter f a n <+: iter f a (n+1) := by
  induction n with
  | zero =>
    change [a] <+: List.flatMap f [a]
    exact ⟨v,by simpa using hf.symm⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨t.flatMap f,?_⟩
    change (iter f a n).flatMap f ++ t.flatMap f = (iter f a (n+1)).flatMap f
    exact List.flatMap_append.symm.trans (congrArg (List.flatMap f) ht)

theorem iter_prefix_le (f : ℤ → List ℤ) (a : ℤ) (v : List ℤ) (hf : f a = a::v)
    {n k : ℕ} (h : n ≤ k) : iter f a n <+: iter f a k := by
  induction h with
  | refl => exact ⟨[],by simp⟩
  | @step k _ ih => exact ih.trans (iter_prefix f a v hf k)

theorem extend_factor (f : ℤ → List ℤ) (a : ℤ) (v : List ℤ)
    (hf : f a = a::v)
    (unbounded : ∀ B : ℕ, ∃ n, B < (iter f a n).length)
    (n : ℕ) (x y z t : List ℤ) (h : iter f a n = x++y++z++t) :
    ∃ (l : ℕ) (r : List ℤ), iter f a l = x++y++z++r ∧ r ≠ [] := by
  obtain ⟨l,hl⟩ := unbounded (iter f a n).length
  have H : n ≤ l := by
    by_contra hn
    have i := iter_prefix_le f a v hf (show l≤n by omega)
    have q := i.length_le
    omega
  obtain ⟨s,hs⟩ := iter_prefix_le f a v hf H
  have ns : s ≠ [] := by
    intro e
    rw [e,List.append_nil] at hs
    rw [← hs] at hl
    omega
  refine ⟨l,t++s,?_,by simp [ns]⟩
  rw [←List.append_assoc,←h]
  exact hs.symm

variable (D : Finset ℤ) (f : ℤ → List ℤ)
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (A : (ℤ×ℤ) →+ (ℤ×ℤ))
variable (aff : ∀ x ∈ D, σ (f x)=A (σ [x]))
variable (u v : ℤ×ℤ) (m : ℤ) (neg : Bool)
variable (a : ℤ) (ha : a∈D)

include aff in
theorem decides_all_factors
    (eU : ∀ p, NeutralTrace.pro u (A p) = sign neg * NeutralTrace.pro u p)
    (eV : ∀ p, NeutralTrace.pro v (A p) = m * NeutralTrace.pro v p)
    (hm : 1 < |m|) (hUV : u.1*v.2-u.2*v.1 ≠ 0)
    (suffix : List ℤ) (hf : f a = a::suffix)
    (unbounded : ∀ B : ℕ, ∃ n, B < (iter f a n).length) :
    decides D f closed u v m neg a ha = true ↔
    ∃ (n : ℕ) (x y z t : List ℤ), iter f a n = x++y++z++t ∧
      0 < y.length ∧ y.length=z.length ∧ y.sum=z.sum := by
  rw [decides_iff D f closed A aff u v m neg a ha eU eV hm hUV]
  constructor
  · rintro ⟨n,x,y,z,t,h,hy,hl,hs,_⟩
    exact ⟨n,x,y,z,t,h,hy,hl,hs⟩
  · rintro ⟨n,x,y,z,t,h,hy,hl,hs⟩
    obtain ⟨l,r,hr,hn⟩ := extend_factor f a suffix hf unbounded n x y z t h
    exact ⟨l,x,y,z,r,hr,hy,hl,hs,hn⟩

end NeutralFixedPoint

#print axioms NeutralFixedPoint.decides_all_factors
