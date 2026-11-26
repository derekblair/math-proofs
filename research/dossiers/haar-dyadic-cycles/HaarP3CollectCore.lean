import HaarCycle
import HaarClass4Powers

namespace HaarP3CollectCore
open HaarClass4CollectCore (Central)
variable {G : Type*} [Group G]

structure Coord where
  k : ℤ
  u : ℤ
  a : ℤ
  z : ℤ
  deriving DecidableEq, Inhabited

structure Base (G : Type*) [Group G] where
  C : G
  U : G
  A : G
  Z : G
  twist : ℤ
  carry : ℤ
  zcent : Central Z
  ca : Commute C A
  ua : Commute U A
  swap : C*U=U*C*Z^twist
  u3 : U^(3:ℤ)=Z^carry
  a3 : A^(3:ℤ)=1
  z3 : Z^(3:ℤ)=1

def ne (M : Base G) (p : Coord) : G :=
  M.C^p.k * M.U^p.u * M.A^p.a * M.Z^p.z

def zero : Coord := ⟨0,0,0,0⟩
def basisC : Coord := ⟨1,0,0,0⟩
def raw (d : ℤ) (p q : Coord) : Coord :=
  ⟨p.k+q.k,p.u+q.u,p.a+q.a,p.z+q.z-d*q.k*p.u⟩

def red (s : ℤ) (p : Coord) : Coord :=
  ⟨p.k,p.u%3,p.a%3,(p.z+(p.u/3)*s)%3⟩

def mul (d s : ℤ) (p q : Coord) := red s (raw d p q)

def neg (d : ℤ) (p : Coord) : Coord :=
  ⟨-p.k,-p.u,-p.a,-p.z-d*p.k*p.u⟩

theorem ne_zero (M : Base G) : ne M zero = 1 := by simp [ne,zero]
theorem ne_C (M : Base G) : ne M basisC = M.C := by simp [ne,basisC]

theorem swap_pows (M : Base G) (u k : ℤ) :
    M.U^u * M.C^k = M.C^k * M.U^u * M.Z^(-M.twist*k*u) := by
  have e := HaarCycle.shift M.C M.U (M.Z^M.twist) ((M.zcent M.C).zpow_left _) M.swap k
  have g : M.U * M.C^k = M.C^k*M.U*M.Z^(-M.twist*k) := by
    change M.C^k * M.U = M.U * M.C^k * (M.Z^M.twist)^k at e
    rw [← zpow_mul] at e
    have zz : M.Z^(-M.twist*k)=(M.Z^(M.twist*k))⁻¹ := by
      rw [show -M.twist*k=-(M.twist*k) by ring,zpow_neg]
    calc
      M.U*M.C^k = (M.U*M.C^k)*(M.Z^(M.twist*k)*(M.Z^(M.twist*k))⁻¹) := by simp
      _ = M.C^k*M.U*M.Z^(-M.twist*k) := by rw [← mul_assoc,←e,zz]
  have e2 := HaarCycle.shift M.U (M.C^k) (M.Z^(-M.twist*k))
    ((M.zcent M.U).zpow_left _) g u
  rw [← zpow_mul] at e2
  simpa only [mul_assoc] using e2

theorem ne_raw (M : Base G) (p q : Coord) :
    ne M (raw M.twist p q) = ne M p * ne M q := by
  let C₁ := M.C^p.k
  let C₂ := M.C^q.k
  let U₁ := M.U^p.u
  let U₂ := M.U^q.u
  let A₁ := M.A^p.a
  let A₂ := M.A^q.a
  let Z₁ := M.Z^p.z
  let Z₂ := M.Z^q.z
  let W := M.Z^(-M.twist*q.k*p.u)
  have cz (n : ℤ) (w : G) : Commute (M.Z^n) w := (M.zcent w).zpow_left _
  have mvA : Commute A₁ (C₂*U₂) :=
    (M.ca.symm.zpow_zpow p.a q.k).mul_right (M.ua.symm.zpow_zpow p.a q.u)
  have mv : Commute (A₁*Z₁) (C₂*U₂) := mvA.mul_left (cz _ _)
  have mvZ : Commute Z₁ A₂ := cz _ _
  have mvW : Commute W (U₂*A₁*A₂*Z₁*Z₂) := cz _ _
  have eZ : U₁*C₂=C₂*U₁*W := swap_pows M p.u q.k
  symm
  calc
    ne M p * ne M q = (C₁*U₁)*((A₁*Z₁)*(C₂*U₂))*(A₂*Z₂) := by
      simp only [ne,C₁,C₂,U₁,U₂,A₁,A₂,Z₁,Z₂,mul_assoc]
    _ = (C₁*(U₁*C₂)*U₂*A₁)*(Z₁*A₂)*Z₂ := by rw [mv.eq]; simp only [mul_assoc]
    _ = (C₁*(C₂*U₁*W))*(U₂*A₁*A₂*Z₁*Z₂) := by rw [mvZ.eq,eZ]; simp only [mul_assoc]
    _ = (C₁*C₂)*(U₁*U₂)*(A₁*A₂)*(Z₁*Z₂*W) := by
      calc
        _ = (C₁*C₂*U₁)*(W*(U₂*A₁*A₂*Z₁*Z₂)) := by simp only [mul_assoc]
        _ = _ := by rw [mvW.eq]; simp only [mul_assoc]
    _ = ne M (raw M.twist p q) := by
      simp only [C₁,C₂,U₁,U₂,A₁,A₂,Z₁,Z₂,W,ne,raw,zpow_add,sub_eq_add_neg,mul_assoc]
      rw [show -(M.twist*(q.k*p.u))= -M.twist*(q.k*p.u) by ring]

theorem pow_period (g : G) (h : g^(3:ℤ)=1) (e : ℤ) : g^(e%3)=g^e := by
  conv_rhs => rw [show e=e%3+3*(e/3) by omega]
  rw [zpow_add,zpow_mul,h,one_zpow,mul_one]

theorem ne_red (M : Base G) (p : Coord) : ne M (red M.carry p) = ne M p := by
  have hu : M.U^p.u = M.U^(p.u%3)*M.Z^((p.u/3)*M.carry) := by
    conv_lhs => rw [show p.u=p.u%3+3*(p.u/3) by omega]
    rw [zpow_add,zpow_mul,M.u3,←zpow_mul,mul_comm M.carry]
  rw [ne,ne,red]
  simp only
  rw [pow_period _ M.a3,pow_period _ M.z3, hu,zpow_add]
  have h := ((M.zcent (M.A^p.a)).zpow_left ((p.u/3)*M.carry)).eq
  have swap := ((Commute.refl M.Z).zpow_zpow p.z ((p.u/3)*M.carry)).eq
  simp only [mul_assoc]
  rw [←mul_assoc (M.Z^((p.u/3)*M.carry)) (M.A^p.a),h,mul_assoc (M.A^p.a),swap]

theorem ne_mul (M : Base G) (p q : Coord) :
    ne M (mul M.twist M.carry p q)=ne M p*ne M q :=
  (ne_red M _).trans (ne_raw M p q)

theorem ne_neg (M : Base G) (p : Coord) : ne M (neg M.twist p) = (ne M p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← ne_raw]
  have E : raw M.twist p (neg M.twist p)=zero := by
    rcases p with ⟨k,u,a,z⟩
    simp [raw,neg,zero]
    ring
  rw [E,ne_zero]

def powN (d s : ℤ) (a : Coord) : ℕ→Coord
  | 0 => zero
  | n+1 => mul d s (powN d s a n) a

def powZ (d s : ℤ) (a : Coord) : ℤ→Coord
  | .ofNat n => powN d s a n
  | .negSucc n => powN d s (neg d a) (n+1)

theorem ne_powN (M : Base G) (p : Coord) (n : Nat) :
    ne M (powN M.twist M.carry p n) = (ne M p)^n := by
  induction n with
  | zero => simp [powN,ne_zero]
  | succ n ih => rw [powN,ne_mul,ih,pow_succ]

theorem ne_powZ (M : Base G) (p : Coord) (n : Int) :
    ne M (powZ M.twist M.carry p n) = (ne M p)^n := by
  cases n with
  | ofNat n => simp [powZ,ne_powN]
  | negSucc n =>
    simp [powZ,ne_powN,ne_neg,zpow_negSucc,inv_pow]

end HaarP3CollectCore
#print axioms HaarP3CollectCore.ne_powZ
