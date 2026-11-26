import ScalarTrace

namespace NeutralTrace

abbrev Point := ℤ × ℤ

def pro (u p : Point) := u.1*p.1+u.2*p.2
def plus (p q : Point) : Point := (p.1+q.1,p.2+q.2)

def run (A : Point → Point) : Point → List Point → Point
  | p, [] => p
  | p, c::cs => run A (plus (A p) c) cs

theorem proj_run (A : Point → Point) (u : Point) (s : ℤ)
    (eig : ∀ p, pro u (A p) = s*pro u p)
    (p : Point) (cs : List Point) :
    pro u (run A p cs) = ScalarTrace.zeval s (pro u p) (cs.map (pro u)) := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [run, List.map_cons, ScalarTrace.zeval, ih]
    congr 1
    rw [← eig p]
    simp only [pro, plus]
    ring

theorem acceptance_iff (A : Point → Point) (u v : Point) (s a : ℤ)
    (hu : ∀ p, pro u (A p) = s*pro u p)
    (hv : ∀ p, pro v (A p) = a*pro v p)
    (hs : s*s=1) (indep : u.1*v.2-u.2*v.1 ≠ 0)
    (cs : List Point) :
    run A (0,0) cs = (0,0) ↔
      (ScalarTrace.labels s 1 (cs.map (pro u))).sum = 0 ∧
      ScalarTrace.zeval a 0 (cs.map (pro v)) = 0 := by
  have hz (w : Point) : pro w (0,0)=0 := by simp [pro]
  have hpu := proj_run A u s hu (0,0) cs
  have hpv := proj_run A v a hv (0,0) cs
  rw [hz] at hpu hpv
  rw [← ScalarTrace.unit_zero_iff s hs, ← hpu, ← hpv]
  constructor
  · intro h; simp [h,hz]
  · rintro ⟨h₁,h₂⟩
    obtain ⟨h₃,h₄⟩ := NeutralAffine.projections_zero _ _ _ _ _ _ indep h₁ h₂
    exact Prod.ext h₃ h₄

end NeutralTrace

#print axioms NeutralTrace.acceptance_iff
