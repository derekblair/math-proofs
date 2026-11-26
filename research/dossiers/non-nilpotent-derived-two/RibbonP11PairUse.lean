import RibbonP11PairCert
namespace RibbonP11Pair
open RibbonStationaryWord RibbonP11Charts RibbonDerived3 RibbonStationaryChart
variable {G : Type*} [Group G]
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem bad_mul_pow : ∀ i : Fin 16,
    (bad i).1 * ((bad i).1)^9=1 ∧ (bad i).2 * ((bad i).2)^9=1 := by decide +kernel

theorem inv_unit_of {R : Type*} [Monoid R] (u : Rˣ) (v : R) (h : (u:R)*v=1) :
    (↑u⁻¹:R)=v := by
  calc
    _ = (↑u⁻¹:R) * ((u:R)*v) := by rw [h,mul_one]
    _ = v := by simp [←mul_assoc,←Units.val_mul]

structure Coeffs (x y : G) (i : Fin 16) where
  mu : G →* Fˣ
  tau : G → F
  aff : Aff mu tau
  mX : (mu x:F)=(bad i).1
  mY : (mu y:F)=(bad i).2
  tX : tau x=(if (bad i).1=1 then 1 else 0)
  tY : tau y=(if (bad i).1=1 then 0 else 1)

theorem Coeffs.sound {x y : G} {i : Fin 16}
    (c : Coeffs x y i) (k : Count) (p q : Fin 64)
    (e : Ribbon5Bridge.pathAt x y (spec k).T.toArray p.val =
      Ribbon5Bridge.pathAt x y (spec k).T.toArray q.val) :
    point (bad i) k p=point (bad i) k q := by
  have ix := inv_unit_of (c.mu x) ((bad i).1^9) (by rw [c.mX]; exact (bad_mul_pow i).1)
  have iy := inv_unit_of (c.mu y) ((bad i).2^9) (by rw [c.mY]; exact (bad_mul_pow i).2)
  have h := flatPosition_same c.mu c.tau c.aff x y (spec k) p.val q.val e
  simpa only [point,ix,iy,c.mX,c.mY,c.tX,c.tY] using h

theorem two_charts (dnil : DLS G 2=⊥) (x y : G) (i j : Fin 16)
    (lt : i.val<j.val) (a : Coeffs x y i) (b : Coeffs x y j) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  let k := pick i j
  let chart (p : Fin 64) := (point (bad i) k p,point (bad j) k p)
  apply from_state dnil k x y chart
  · exact fun p q e => Prod.ext (a.sound k p q e) (b.sound k p q e)
  · intro p q lp e
    exact certified i j lt p q lp (congrArg Prod.fst e) (congrArg Prod.snd e)

end RibbonP11Pair
#print axioms RibbonP11Pair.two_charts
