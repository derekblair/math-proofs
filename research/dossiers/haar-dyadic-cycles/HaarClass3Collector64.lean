import HaarClass3Collect
import HaarHalfCollision

namespace HaarClass3Collector64
open HaarClass3Collect HaarClass3Table
variable {G : Type*} [Group G]

def Range (i : ℤ) : Prop := i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2

theorem xy_limited (x y c u : G) (huX : Commute u x) (huC : Commute u c)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (i : ℤ) (hi : Range i) :
    x^i*y=y*x^i*c^i*u^(i*(i-1)/2) := by
  rcases hi with t|t|t|t
  · exact pow_trans_limited x y c u huX huC r rx i (Or.inr (Or.inl t))
  · exact pow_trans_limited x y c u huX huC r rx i (Or.inl t)
  · subst i
    norm_num
    exact r
  · subst i
    norm_num
    calc
      x^2*y = x*(x*y) := by rw [pow_two,mul_assoc]
      _ = y*x^2*c^2*u := by
        rw [r]
        simp only [mul_assoc]
        rw [←mul_assoc x y _,r]
        simp only [mul_assoc]
        rw [←mul_assoc c x c,rx]
        simp only [mul_assoc]
        rw [(huC).eq]
        simp [pow_two,mul_assoc]

theorem norm_y (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (p : Coord) (hi : Range p.1) :
    HaarClass3Collect.norm x y c u v (dy p) = HaarClass3Collect.norm x y c u v p * y := by
  let i := p.1
  let k := p.2.2.1
  let a := p.2.2.2.1
  let b := p.2.2.2.2
  let t := i*(i-1)/2
  have hxy : x^i*y=y*x^i*c^i*u^t := xy_limited x y c u (hu x) (hu c) r rx i hi
  have hcy := HaarCycle.shift c y v (hv c) ry k
  have hy : Commute (u^a*v^b) y := ((hu y).zpow_left a).mul_left ((hv y).zpow_left b)
  have huc : Commute (u^t) (c^k) := (hu c).zpow_zpow _ _
  have hva : Commute (v^k) (u^a) := (hv u).zpow_zpow _ _
  have H : x^i*c^k*u^a*v^b*y = y*x^i*c^(k+i)*u^(a+i*(i-1)/2)*v^(b+k) := by
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
  simp only [HaarClass3Collect.norm,dy,zpow_add_one,mul_assoc]
  exact congrArg (fun z => y^p.2.1*z) (by simpa only [mul_assoc] using H.symm)

def mx (p : Coord) : Coord :=
  (p.1-1,p.2.1,p.2.2.1,p.2.2.2.1-p.2.2.1,p.2.2.2.2)

def my (p : Coord) : Coord :=
  (p.1,p.2.1-1,p.2.2.1-p.1,p.2.2.2.1-p.1*(p.1-1)/2,p.2.2.2.2-(p.2.2.1-p.1))

def move (pos : Bool) (port : Fin 3) (p : Coord) : Coord :=
  if port=0 then p else if port=1 then if pos then dx p else mx p else
    if pos then dy p else my p

theorem dx_mx (p : Coord) : dx (mx p)=p := by
  rcases p with ⟨i,j,k,a,b⟩
  simp [dx,mx]

theorem dy_my (p : Coord) : dy (my p)=p := by
  rcases p with ⟨i,j,k,a,b⟩
  simp [dy,my]

theorem norm_move (x y c u v : G)
    (hu : ∀ z : G, Commute u z) (hv : ∀ z : G, Commute v z)
    (r : x*y=y*x*c) (rx : c*x=x*c*u) (ry : c*y=y*c*v)
    (pos : Bool) (port : Fin 3) (p : Coord)
    (hp : port=2 → Range p.1) :
    HaarClass3Collect.norm x y c u v (move pos port p) =
      HaarClass3Collect.norm x y c u v p *
        (if pos then HaarHalfCollision.port x y port else (HaarHalfCollision.port x y port)⁻¹) := by
  have hx := HaarClass3Collect.norm_x x y c u v hu hv rx p
  have hx_inv := HaarClass3Collect.norm_x x y c u v hu hv rx (mx p)
  rw [dx_mx] at hx_inv
  have hy (hr : Range p.1) := norm_y x y c u v hu hv r rx ry p hr
  have hy_inv (hr : Range p.1) := norm_y x y c u v hu hv r rx ry (my p) hr
  have hy_reverse (hr : Range p.1) := (dy_my p) ▸ hy_inv hr
  fin_cases port <;> cases pos
  · simp [move,HaarHalfCollision.port]
  · simp [move,HaarHalfCollision.port]
  · simpa [move,HaarHalfCollision.port] using (eq_mul_inv_iff_mul_eq.mpr hx_inv.symm)
  · simpa [move,HaarHalfCollision.port] using hx
  · simpa [move,HaarHalfCollision.port] using
      (eq_mul_inv_iff_mul_eq.mpr (hy_reverse (hp rfl)).symm)
  · simpa [move,HaarHalfCollision.port] using hy (hp rfl)

end HaarClass3Collector64
#print axioms HaarClass3Collector64.norm_move
