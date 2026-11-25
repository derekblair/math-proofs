import Density
import LocalArea
import OrderBounds
import Limit

namespace PermCircles
open Filter Real MeasureTheory Set
open scoped Topology ENNReal BigOperators

def MinPacking (r : ℝ) {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  2 ≤ n ∧ (∀ i j, i ≠ j → 4*r^2 ≤ sqDist (center p i) (center p j)) ∧
    ∀ m, Fits r m → n ≤ m

theorem minimum_exists {r : ℝ} (hr : 1 ≤ r) :
    ∃ (n : ℕ) (p : Equiv.Perm (Fin n)), MinPacking r p := by
  classical
  obtain ⟨n,hn,_⟩ := radius_order hr
  have hex : ∃ n, Fits r n := ⟨n,hn⟩
  have hnmin := Nat.find_spec hex
  rcases hnmin with ⟨hN,p,hp⟩
  exact ⟨Nat.find hex,p,hN,hp,fun m hm => Nat.find_min' hex hm⟩

lemma order_lower {r : ℝ} (hr : 1 ≤ r) {n : ℕ} {p : Equiv.Perm (Fin n)}
    (hn : 2 ≤ n) (hp : ∀ i j, i ≠ j → 4*r^2 ≤ sqDist (center p i) (center p j)) :
    2*sqrt 3*r^2-(8/sqrt 3+16/3)*r ≤ (n:ℝ) := by
  let R := 2*r/sqrt 3
  let M := (n:ℝ)-1
  have hS0 : 0 < sqrt 3 := sqrt_pos.2 (by norm_num)
  have hS : (sqrt 3)^2 = 3 := sq_sqrt (by norm_num)
  have hr0 : 0 < r := by linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hR2 : R^2=4*r^2/3 := by
    dsimp [R]
    rw [div_pow,hS]
    ring
  have hV : 0 ≤ 2*sqrt 3*r^2 := by positivity
  have hM : 0 ≤ M := by
    have hh : (2:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [M]; linarith
  have hc (i : Fin n) : ENNReal.ofReal (2*sqrt 3*r^2) ≤ volume (cell R (center p) i) := by
    rw [← volume_cell_translate]
    exact volume_localCell_lower hr0 hR hR2 _ hp i
  have ha := global_area_from_cells hR.le hM hV (center p) (centers_fst_injective p) (centers_in_box p) hc
  apply finite_to_order_lower hr ⟨hn,p,hp⟩
  have hh : (M+2*R)^2 ≤ ((n:ℝ)+4*r/sqrt 3)^2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    dsimp [M,R]
    ring_nf
    linarith
  nlinarith [ha.trans hh]

lemma order_upper {r : ℝ} (hr : 1 ≤ r) {n : ℕ} {p : Equiv.Perm (Fin n)}
    (h : MinPacking r p) :
    (n:ℝ) ≤ 2*sqrt 3*r^2+(5*sqrt 3+3)*r+(3*sqrt 3+5) := by
  obtain ⟨m,hm,hh⟩ := radius_order hr
  exact (by exact_mod_cast (h.2.2 m hm) : (n:ℝ) ≤ (m:ℝ)).trans hh

/-- Permuted circle packing, BHT Question 5.5, for every selection of
    nondegenerate minimum packings. A genuine limit, not only liminf. -/
theorem question55 {n : ℝ → ℕ} (p : ∀ r, Equiv.Perm (Fin (n r)))
    (h : ∀ᶠ r in atTop, MinPacking r (p r)) :
    Tendsto (fun r => clippedDensity r (p r)) atTop (𝓝 (π/(2*sqrt 3))) := by
  have hLo : ∀ᶠ r in atTop, 2*sqrt 3*r^2-(8/sqrt 3+16/3)*r ≤ (n r:ℝ) := by
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with r hp hr
    exact order_lower hr hp.1 hp.2.1
  have hHi : ∀ᶠ r in atTop, (n r:ℝ) ≤ 2*sqrt 3*r^2+(5*sqrt 3+3)*r+(3*sqrt 3+5) := by
    filter_upwards [h,eventually_ge_atTop (1:ℝ)] with r hp hr
    exact order_upper hr hp
  have hn := norm_order_limit hLo hHi
  have hDLo : ∀ᶠ r in atTop, π*r^2*((n r:ℝ)-4*r-4)/((n r:ℝ)-1)^2 ≤ clippedDensity r (p r) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    exact (density_bounds hr (p r)).1
  have hDHi : ∀ᶠ r in atTop, clippedDensity r (p r) ≤ π*r^2*(n r:ℝ)/((n r:ℝ)-1)^2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    exact (density_bounds hr (p r)).2
  exact clipped_density_limit (by positivity) hn hDLo hDHi

#print axioms question55
end PermCircles
