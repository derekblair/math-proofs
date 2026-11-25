import PlaneMeasure
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace PermCircles
open Set Function

noncomputable def planeComplex : Point ≃ₜ ℂ :=
  Complex.equivRealProdCLM.symm.toHomeomorph

lemma dist_complex_sq (x y : Point) :
    (dist (planeComplex x) (planeComplex y))^2 = sqDist x y := by
  rw [Complex.dist_eq,Complex.sq_norm,Complex.normSq_apply]
  have hre (p : Point) : (planeComplex p).re = p.1 := by rfl
  have him (p : Point) : (planeComplex p).im = p.2 := by rfl
  simp [sqDist,hre,him]
  ring

lemma disk_is_complex_ball {r : ℝ} (hr : 0 ≤ r) (p : Point) :
    disk r p = planeComplex ⁻¹' Metric.closedBall (planeComplex p) r := by
  ext z
  change sqDist z p ≤ r^2 ↔ dist (planeComplex z) (planeComplex p) ≤ r
  rw [←dist_complex_sq]
  exact sq_le_sq₀ dist_nonneg hr

lemma interior_disk {r : ℝ} (hr : 0 < r) (p : Point) :
    interior (disk r p) = {z | sqDist z p < r^2} := by
  rw [disk_is_complex_ball hr.le, ← planeComplex.preimage_interior,
    interior_closedBall (planeComplex p) hr.ne']
  ext z
  change dist (planeComplex z) (planeComplex p) < r ↔ sqDist z p < r^2
  rw [←dist_complex_sq]
  exact (sq_lt_sq₀ dist_nonneg hr.le).symm

lemma disjoint_interiors_iff {r : ℝ} (hr : 0 < r) (p q : Point) :
    Disjoint (interior (disk r p)) (interior (disk r q)) ↔ 4*r^2 ≤ sqDist p q := by
  rw [interior_disk hr p,interior_disk hr q]
  constructor
  · intro h
    by_contra! hl
    let z : Point := ((p.1+q.1)/2,(p.2+q.2)/2)
    have hp : sqDist z p = sqDist p q/4 := by dsimp [z,sqDist]; ring
    have hq : sqDist z q = sqDist p q/4 := by dsimp [z,sqDist]; ring
    have hz1 : z ∈ {z | sqDist z p < r^2} := by change sqDist z p < r^2; linarith
    have hz2 : z ∈ {z | sqDist z q < r^2} := by change sqDist z q < r^2; linarith
    exact Set.disjoint_left.mp h hz1 hz2
  · intro hd
    apply Set.disjoint_left.mpr
    intro z hp hq
    change sqDist z p < r^2 at hp
    change sqDist z q < r^2 at hq
    have he : 2*(sqDist z p+sqDist z q)-sqDist p q =
      (2*z.1-p.1-q.1)^2+(2*z.2-p.2-q.2)^2 := by unfold sqDist; ring
    linarith [sq_nonneg (2*z.1-p.1-q.1),sq_nonneg (2*z.2-p.2-q.2)]

#print axioms disjoint_interiors_iff

end PermCircles
