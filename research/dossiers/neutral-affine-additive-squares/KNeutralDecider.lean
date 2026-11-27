import KPhaseFinite

namespace KNeutralDecider
open KPhase KPhaseFinite KProjection

variable {D : Finset ℤ} {f : ℤ → List ℤ} {k : ℕ}
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (u v : ℤ × ℤ) (neg : Bool) (m B : ℤ)

def acceptBetween (arcList : List (Arc D f k v m B)) (vertexList : List (Vertex D k B))
    (x y : Q D k) (z : 0 ∈ IntegerTrace.box B) : Bool :=
  [false,true].any fun q =>
    VectorWalk.decideWalk (src (D:=D) (f:=f) v m B) (dst closed v neg m B) (label u v neg m B)
      arcList vertexList (target B x z false) (target B y z q) 0

theorem acceptBetween_iff (arcList : List (Arc D f k v m B)) (vertexList : List (Vertex D k B))
    (hA : ∀ e, e ∈ arcList) (hV : ∀ e, e ∈ vertexList) (x y : Q D k)
    (z : 0 ∈ IntegerTrace.box B) :
    acceptBetween closed u v neg m B arcList vertexList x y z = true ↔
    ∃ q, VW closed u v neg m B (target B x z false) (target B y z q) 0 := by
  simp only [acceptBetween,List.any_eq_true,VectorWalk.decideWalk_correct _ _ _ _ _ hA hV]
  constructor
  · rintro ⟨q,_,h⟩; exact ⟨q,h⟩
  · rintro ⟨q,h⟩
    exact ⟨q,by cases q <;> simp,h⟩

open KCut

def decidePower (a : ℤ) (ha : a ∈ D) (z : 0 ∈ IntegerTrace.box B)
    (arcList : List (Arc D f k v m B)) (vertexList : List (Vertex D k B)) (stateList : List (Q D k)) : Bool :=
  stateList.any fun y => decide (y.2 = fun _ => true) &&
    acceptBetween closed u v neg m B arcList vertexList (KTrace.vertex closed a ha (d:=0) (root a)) y z

theorem decidePower_correct (a : ℤ) (ha : a ∈ D) (z : 0 ∈ IntegerTrace.box B)
    (arcList : List (Arc D f k v m B)) (vertexList : List (Vertex D k B)) (stateList : List (Q D k))
    (hA : ∀ e, e ∈ arcList) (hV : ∀ e, e ∈ vertexList) (hQ : ∀ e, e ∈ stateList)
    (A : (ℤ × ℤ) →+ (ℤ × ℤ)) (aff : ∀ x ∈ D, AffineAddress.σ (f x) = A (AffineAddress.σ [x]))
    (hu : ∀ p, NeutralTrace.pro u (A p) = PhaseProduct.sign neg * NeutralTrace.pro u p)
    (hv : ∀ p, NeutralTrace.pro v (A p) = m * NeutralTrace.pro v p)
    (indep : u.1*v.2-u.2*v.1 ≠ 0) (C : ℤ)
    (hE : ∀ (e : E D f k) (j : Fin k), |ex v j e| ≤ C)
    (hm : 1 < |m|) (hB : 0 ≤ B) (hc : C ≤ (|m|-1)*B) :
    decidePower closed u v neg m B a ha z arcList vertexList stateList = true ↔
      ∃ d, KFactors.Actual (TripTrace.iter f a d) k := by
  rw [← KTrace.path_iff_actual closed A aff a ha]
  set x := KTrace.vertex closed a ha (d:=0) (root a : Chain [a] (k+1))
  unfold decidePower
  simp only [List.any_eq_true,hQ,true_and,Bool.and_eq_true,decide_eq_true_eq,
    acceptBetween_iff closed u v neg m B _ _ hA hV,
    criterion closed u v neg m B _ _ z C hE hm hB hc,
    projected_zero A u v neg m hu hv indep]
  constructor
  · rintro ⟨y, hy, L, p, n, e⟩
    exact ⟨y,L,p,hy,n,e⟩
  · rintro ⟨y,L,p,hy,n,e⟩
    exact ⟨y,hy,L,p,n,e⟩

end KNeutralDecider

#print axioms KNeutralDecider.acceptBetween_iff
#print axioms KNeutralDecider.decidePower_correct
