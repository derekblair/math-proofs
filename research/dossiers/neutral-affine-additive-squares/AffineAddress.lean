import Mathlib.Tactic

namespace AffineAddress

def σ (w : List ℤ) : ℤ × ℤ := ((w.length:ℤ),w.sum)

theorem sig_append (u v : List ℤ) : σ (u++v) = σ u+σ v := by
  apply Prod.ext <;> simp [σ]

theorem sig_exp (f : ℤ → List ℤ) (A : (ℤ × ℤ) →+ (ℤ × ℤ))
    (aff : ∀ x, σ (f x) = A (σ [x])) (u : List ℤ) :
    σ (u.flatMap f) = A (σ u) := by
  induction u with
  | nil => exact (map_zero A).symm
  | cons x u ih =>
    rw [List.flatMap_cons, sig_append, aff, ih, ← map_add]
    rw [← sig_append]; rfl

theorem take_image (f : ℤ → List ℤ) (u v : List ℤ) (x : ℤ) (r : ℕ)
    (hr : r ≤ (f x).length) :
    ((u++x::v).flatMap f).take ((u.flatMap f).length+r)
      = u.flatMap f ++ (f x).take r := by
  rw [List.flatMap_append, List.flatMap_cons, List.take_append]
  have e : (u.flatMap f).length+r-(u.flatMap f).length=r := by omega
  rw [e,List.take_append_of_le_length hr]
  simp

theorem address_exists (f : ℤ → List ℤ) (w : List ℤ) (j : ℕ)
    (hj : j < (w.flatMap f).length) :
    ∃ u x v r, w=u++x::v ∧ r<(f x).length ∧ j=(u.flatMap f).length+r := by
  induction w generalizing j with
  | nil => simp at hj
  | cons x v ih =>
    rw [List.flatMap_cons,List.length_append] at hj
    by_cases h : j < (f x).length
    · exact ⟨[],x,v,j,rfl,h,by simp⟩
    · obtain ⟨u,y,t,r,fact,sub,addr⟩ :=
        ih (j-(f x).length) (by omega)
      refine ⟨x::u,y,t,r,?_,sub,?_⟩
      · simp [fact]
      · simp only [List.flatMap_cons,List.length_append]; omega

theorem prefix_step (f : ℤ → List ℤ) (A : (ℤ × ℤ) →+ (ℤ × ℤ))
    (aff : ∀ x, σ (f x) = A (σ [x]))
    (u v : List ℤ) (x : ℤ) (r : ℕ) (hr : r < (f x).length) :
    σ (((u++x::v).flatMap f).take ((u.flatMap f).length+r))
      = A (σ u)+σ ((f x).take r) := by
  rw [take_image f u v x r hr.le, sig_append, sig_exp f A aff]

theorem diff_step (A : (ℤ × ℤ) →+ (ℤ × ℤ)) (a b c x y z : ℤ × ℤ) :
    (A a+x)+(A c+z)-((A b+y)+(A b+y)) =
      A (a+c-(b+b)) + (x+z-(y+y)) := by
  simp only [map_add,map_sub]
  abel

theorem diff_zero_iff (u v w : List ℤ) :
    σ u + σ w - (σ v + σ v) = 0 ↔
      ((u.length:ℤ)+(w.length:ℤ)=2*(v.length:ℤ)) ∧
       u.sum+w.sum=2*v.sum := by
  constructor
  · intro h
    have a := congrArg Prod.fst h
    have b := congrArg Prod.snd h
    simp [σ] at a b
    exact ⟨by omega,by omega⟩
  · rintro ⟨ha,hb⟩
    apply Prod.ext <;> simp [σ] <;> omega

end AffineAddress

#print axioms AffineAddress.sig_exp
#print axioms AffineAddress.address_exists
#print axioms AffineAddress.prefix_step
#print axioms AffineAddress.diff_step
#print axioms AffineAddress.diff_zero_iff
