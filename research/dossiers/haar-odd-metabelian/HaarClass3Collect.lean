import HaarClass3Table

namespace HaarClass3Collect
open HaarClass3Table

variable {G : Type*} [Group G]

theorem swap_inv (x c u : G) (huX : Commute u x) (huC : Commute u c)
    (rel : c*x=x*c*u) : c⁻¹*x⁻¹=x⁻¹*c⁻¹*u := by
  have h : x⁻¹*c⁻¹ = u⁻¹*(c⁻¹*x⁻¹) := by
    simpa only [mul_inv_rev,mul_assoc] using congrArg (fun w : G => w⁻¹) rel
  calc
    c⁻¹*x⁻¹ = u*(x⁻¹*c⁻¹) := by rw [h,← mul_assoc,mul_inv_cancel,one_mul]
    _ = (x⁻¹*c⁻¹)*u := ((huX.inv_right).mul_right (huC.inv_right)).eq

theorem pow_trans_limited (x y c u : G)
    (huX : Commute u x) (huC : Commute u c)
    (rel : x*y=y*x*c) (rel2 : c*x=x*c*u)
    (i : ℤ) (ranges : i=0 ∨ i= -1 ∨ i= -2) :
    x^i*y = y*x^i*c^i*u^(i*(i-1)/2) := by
  have hS : SemiconjBy y (x*c) x := by
    change y*(x*c) = x*y
    rw [rel,mul_assoc]
  have hpow := (hS.zpow_right i).eq
  have hInv := swap_inv x c u huX huC rel2
  rcases ranges with rfl | rfl | rfl
  · simp
  · have hpow' : y*(x*c)⁻¹ = x⁻¹*y := by simpa using hpow
    calc
      x^(-1:ℤ)*y = y*(x*c)⁻¹ := by simpa using hpow'.symm
      _ = y*(x⁻¹*c⁻¹*u) := by rw [mul_inv_rev,hInv]
      _ = y*x^(-1:ℤ)*c^(-1:ℤ)*u^(((-1:ℤ)*(-1-1))/2) := by norm_num [mul_assoc]
  · have w : (x*c)^(-2:ℤ) = x^(-2:ℤ)*c^(-2:ℤ)*u^ (3:ℤ) := by
      rw [show (-2:ℤ)=(-1)+(-1) by decide,zpow_add]
      simp only [zpow_neg_one,mul_inv_rev]
      rw [hInv]
      have ux := huX.inv_right.eq
      have uc := huC.inv_right.eq
      calc
        (x⁻¹*c⁻¹*u)*(x⁻¹*c⁻¹*u) = x⁻¹*c⁻¹*x⁻¹*c⁻¹*u*u := by
          simp only [mul_assoc]
          rw [← mul_assoc u x⁻¹ _,ux,mul_assoc x⁻¹ u _,← mul_assoc u c⁻¹ _,uc]
          simp only [mul_assoc]
        _ = x⁻¹*(c⁻¹*x⁻¹)*c⁻¹*u*u := by group
        _ = x⁻¹*(x⁻¹*c⁻¹*u)*c⁻¹*u*u := by rw [hInv]
        _ = x^(-2:ℤ)*c^(-2:ℤ)*u^(3:ℤ) := by
          simp only [mul_assoc]
          rw [← mul_assoc u c⁻¹ _,uc]
          group
          norm_num [pow_succ, mul_assoc]
    calc
      x^(-2:ℤ)*y = y*(x*c)^(-2:ℤ) := hpow.symm
      _ = y*x^(-2:ℤ)*c^(-2:ℤ)*u^(((-2:ℤ)*(-2-1))/2) := by rw [w]; norm_num [mul_assoc]

def norm (x y c u v : G) (p : Coord) :=
  y^p.2.1 * x^p.1 * c^p.2.2.1 * u^p.2.2.2.1 * v^p.2.2.2.2

theorem prefix_norm_x (x c u v : G) (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : c*x=x*c*u) (i k a b : ℤ) :
    x^i*c^k*u^a*v^b*x = x^(i+1)*c^k*u^(a+k)*v^b := by
  have h := HaarCycle.shift c x u (hu c) r k
  have hx : Commute (u^a*v^b) x := ((hu x).zpow_left a).mul_left ((hv x).zpow_left b)
  have hxk : Commute (u^a) (u^k) := (Commute.refl u).zpow_zpow _ _
  calc
    x^i*c^k*u^a*v^b*x = x^i*c^k*((u^a*v^b)*x) := by simp only [mul_assoc]
    _ = x^i*(c^k*x)*(u^a*v^b) := by rw [hx.eq]; simp only [mul_assoc]
    _ = x^i*(x*c^k*u^k)*(u^a*v^b) := by rw [h]
    _ = x^(i+1)*c^k*u^(a+k)*v^b := by
      rw [zpow_add_one,zpow_add,hxk.eq]
      simp only [mul_assoc]

theorem prefix_norm_y (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (i k a b : ℤ) (hi : i=0 ∨ i= -1 ∨ i= -2) :
    x^i*c^k*u^a*v^b*y = y*x^i*c^(k+i)*u^(a+i*(i-1)/2)*v^(b+k) := by
  let t : ℤ := i*(i-1)/2
  have hxy : x^i*y=y*x^i*c^i*u^t := pow_trans_limited x y c u (hu x) (hu c) r rx i hi
  have hcy := HaarCycle.shift c y v (hv c) ry k
  have hy : Commute (u^a*v^b) y := ((hu y).zpow_left a).mul_left ((hv y).zpow_left b)
  have huc : Commute (u^t) (c^k) := (hu c).zpow_zpow _ _
  have hva : Commute (v^k) (u^a) := (hv u).zpow_zpow _ _
  calc
    x^i*c^k*u^a*v^b*y = x^i*c^k*((u^a*v^b)*y) := by simp only [mul_assoc]
    _ = x^i*(c^k*y)*(u^a*v^b) := by rw [hy.eq]; simp only [mul_assoc]
    _ = (x^i*y)*c^k*v^k*u^a*v^b := by rw [hcy]; simp only [mul_assoc]
    _ = (y*x^i*c^i*u^t)*c^k*v^k*u^a*v^b := by rw [hxy]
    _ = (y*x^i)*(c^i*c^k)*(u^t*u^a)*(v^k*v^b) := by
      simp only [mul_assoc]
      rw [← mul_assoc (u^t) (c^k) _,huc.eq,mul_assoc (c^k) (u^t) _]
      rw [← mul_assoc (v^k) (u^a) _,hva.eq]
      simp only [mul_assoc]
    _ = y*x^i*c^(k+i)*u^(a+i*(i-1)/2)*v^(b+k) := by
      rw [show k+i=i+k by omega,show a+i*(i-1)/2=t+a by dsimp [t]; omega,
        show b+k=k+b by omega,zpow_add,zpow_add,zpow_add]

theorem norm_x (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : c*x=x*c*u) (p : Coord) :
    norm x y c u v (dx p) = norm x y c u v p * x := by
  simp only [norm,dx, mul_assoc]
  exact congrArg (fun z => y^p.2.1*z)
    (by simpa only [mul_assoc] using (prefix_norm_x x c u v hu hv r p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).symm)

theorem norm_y (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (p : Coord) (hi : p.1=0 ∨ p.1= -1 ∨ p.1= -2) :
    norm x y c u v (dy p) = norm x y c u v p * y := by
  simp only [norm,dy,zpow_add_one,mul_assoc]
  exact congrArg (fun z => y^p.2.1*z)
    (by simpa only [mul_assoc] using
      (prefix_norm_y x y c u v hu hv r rx ry p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 hi).symm)

end HaarClass3Collect

#print axioms HaarClass3Collect.pow_trans_limited

#print axioms HaarClass3Collect.norm_x
#print axioms HaarClass3Collect.norm_y
