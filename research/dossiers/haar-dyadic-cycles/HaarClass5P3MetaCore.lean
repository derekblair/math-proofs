import HaarClass4Data
import HaarHalfCollision

namespace HaarClass5P3Meta
open HaarClass4Data
variable {G : Type*} [Group G]

abbrev Triple := ℤ × ℤ × ℤ
abbrev Row := ℤ × ℤ × Triple

structure Model (G : Type*) [Group G] where
  x : G
  y : G
  c : G
  u : G
  A : G
  cu : Commute c u
  ca : Commute c A
  ua : Commute u A
  xy : x*y=y*x*c
  U9 : u^(9:ℕ)=1
  A3 : A^(3:ℕ)=1
  xc : rc x⁻¹ c = c*u⁻¹
  xu : rc x⁻¹ u = u*A⁻¹
  xa : rc x⁻¹ A = A*u^(3:ℕ)
  yc : rc y⁻¹ c = c*u^(-2:ℤ)*A
  yu : rc y⁻¹ u = u^(-2:ℤ)*A
  ya : rc y⁻¹ A = A*u^(-3:ℤ)

def tripAdd (p q : Triple) : Triple := (p.1+q.1,p.2.1+q.2.1,p.2.2+q.2.2)
def scale (i : ℤ) (p : Triple) : Triple := (i*p.1,i*p.2.1,i*p.2.2)
def cap (p : Triple) : Triple := (p.1,p.2.1%9,p.2.2%3)

variable (M : Model G)
def D (p : Triple) : G := M.c^p.1*M.u^p.2.1*M.A^p.2.2
def eval (p : Row) : G := M.y^p.2.1*M.x^p.1*D M p.2.2

theorem dadd (p q : Triple) : D M (tripAdd p q)=D M p*D M q := by
  have swap {a b : G} (h : a*b=b*a) (c : G) : a*(b*c)=b*(a*c) := by rw [←mul_assoc,h,mul_assoc]
  simp only [D,tripAdd,zpow_add,mul_assoc]
  rw [swap ((M.cu.zpow_zpow q.1 p.2.1).eq),swap ((M.ua.zpow_zpow q.2.1 p.2.2).eq),
    swap ((M.ca.zpow_zpow q.1 p.2.2).eq)]

theorem dscale (i : ℤ) (p : Triple) : D M (scale i p)=(D M p)^i := by
  have h₁ : Commute (M.c^p.1) (M.u^p.2.1) := M.cu.zpow_zpow _ _
  have h₂ : Commute (M.c^p.1*M.u^p.2.1) (M.A^p.2.2) :=
    (M.ca.zpow_zpow _ _).mul_left (M.ua.zpow_zpow _ _)
  simp only [D,scale,h₂.mul_zpow,h₁.mul_zpow,←zpow_mul]
  rw [mul_comm i p.1,mul_comm i p.2.1,mul_comm i p.2.2]

theorem pow_mod (x : G) (n : ℤ) (hn : x^n=1) (i : ℤ) : x^(i%n)=x^i := by
  have hi : i % n + n*(i/n)=i := Int.emod_add_mul_ediv i n
  calc
    x^(i%n) = x^(i%n)*x^(n*(i/n)) := by rw [zpow_mul,hn,one_zpow,mul_one]
    _ = x^i := by rw [←zpow_add,hi]

theorem dcap (p : Triple) : D M (cap p) = D M p := by
  have h9 : M.u^(9:ℤ)=1 := by exact_mod_cast M.U9
  have h3 : M.A^(3:ℤ)=1 := by exact_mod_cast M.A3
  simp only [D,cap,pow_mod M.u 9 h9,pow_mod M.A 3 h3]

theorem map_D (f : G →* G) (p C U A : Triple)
    (hc : f M.c = D M C) (hu : f M.u = D M U) (ha : f M.A = D M A) :
    f (D M p) = D M (tripAdd (tripAdd (scale p.1 C) (scale p.2.1 U)) (scale p.2.2 A)) := by
  rw [dadd,dadd,dscale,dscale,dscale]
  simp only [D,map_mul,map_zpow,hc,hu,ha]

def leftX (p : Triple) : Triple := (p.1,p.2.1-p.1+3*p.2.2,p.2.2-p.2.1)
def leftY (p : Triple) : Triple := (p.1,-2*p.1-2*p.2.1-3*p.2.2,p.1+p.2.1+p.2.2)

theorem leftX_eval (p : Triple) : rc M.x⁻¹ (D M p) = D M (leftX p) := by
  have h := map_D M (rc M.x⁻¹) p (1,-1,0) (0,1,-1) (0,3,1)
    (by simpa [D] using M.xc) (by simpa [D] using M.xu) (by
      have h := M.xa
      rw [←(M.ua.pow_left 3).eq] at h
      simpa [D] using h)
  rw [h]
  congr 1
  simp [tripAdd,scale,leftX]; ring_nf; simp

theorem leftY_eval (p : Triple) : rc M.y⁻¹ (D M p) = D M (leftY p) := by
  have h := map_D M (rc M.y⁻¹) p (1,-2,1) (0,-2,1) (0,-3,1)
    (by simpa [D] using M.yc) (by simpa [D] using M.yu)
    (by
      have h := M.ya
      rw [←(M.ua.zpow_left (-3)).eq] at h
      simpa [D] using h)
  rw [h]
  congr 1
  simp [tripAdd,scale,leftY]; ring

end HaarClass5P3Meta
#print axioms HaarClass5P3Meta.leftX_eval
#print axioms HaarClass5P3Meta.leftY_eval
