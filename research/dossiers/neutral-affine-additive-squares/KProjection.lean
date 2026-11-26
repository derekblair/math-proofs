import KTrace
import IntegerTrace
import VectorWalk

namespace KProjection
open NeutralTrace
open PhaseProduct (sign sign_sq)

variable {D : Finset ℤ} {f : ℤ → List ℤ} {k : ℕ}
variable (A : (ℤ × ℤ) →+ (ℤ × ℤ))
variable (u v : ℤ × ℤ) (neg : Bool) (m : ℤ)

def ex (j : Fin k) (e : KTrace.Ed D f k) := pro v (KFinite.stamp e j)
def nu (j : Fin k) (e : KTrace.Ed D f k) := pro u (KFinite.stamp e j)

theorem projected_zero (hu : ∀ p, pro u (A p) = sign neg * pro u p)
    (hv : ∀ p, pro v (A p) = m * pro v p)
    (indep : u.1*v.2-u.2*v.1 ≠ 0)
    (L : List (KTrace.Ed D f k)) :
    KTrace.run A 0 L = 0 ↔
      (∀ j : Fin k, ScalarTrace.zeval (sign neg) 0 (L.map (nu u j)) = 0) ∧
      (∀ j : Fin k, ScalarTrace.zeval m 0 (L.map (ex v j)) = 0) := by
  have each (j : Fin k) :
      KTrace.run A 0 L j = 0 ↔
      ScalarTrace.zeval (sign neg) 0 (L.map (nu u j)) = 0 ∧
      ScalarTrace.zeval m 0 (L.map (ex v j)) = 0 := by
    change NeutralTrace.run A (0,0) _ = (0,0) ↔ _
    unfold nu ex
    simpa only [List.map_map,Function.comp_def,nu,ex,← ScalarTrace.unit_zero_iff _ (sign_sq neg)]
      using NeutralTrace.acceptance_iff A u v (sign neg) m hu hv (sign_sq neg) indep
        (L.map (fun e => KFinite.stamp e j))
  constructor
  · intro h
    have hh (j : Fin k) := (each j).mp (congrFun h j)
    exact ⟨fun j => (hh j).1, fun j => (hh j).2⟩
  · rintro ⟨h,h'⟩
    exact funext (fun j => (each j).mpr ⟨h j,h' j⟩)

theorem all_prefix (B C : ℤ) (hm : 1 < |m|) (hB : 0 ≤ B) (hc : C ≤ (|m|-1)*B)
    (hE : ∀ (e : KTrace.Ed D f k) (j : Fin k), |ex v j e| ≤ C)
    (L U V : List (KTrace.Ed D f k)) (hh : L = U ++ V)
    (hzero : ∀ j : Fin k, ScalarTrace.zeval m 0 (L.map (ex v j)) = 0) :
    ∀ j : Fin k, ScalarTrace.zeval m 0 (U.map (ex v j)) ∈ IntegerTrace.box B := by
  intro j
  apply IntegerTrace.can_clip m B C hm hB hc _ (V.map (ex v j))
  · intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hE i j
  · simpa only [hh,List.map_append] using hzero j

end KProjection

#print axioms KProjection.projected_zero
#print axioms KProjection.all_prefix
