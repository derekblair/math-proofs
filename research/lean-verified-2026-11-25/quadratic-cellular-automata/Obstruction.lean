import Quotient
import Mathlib.Tactic.Linarith
namespace QuadraticCA

theorem iterated_polar_zero (r : ℕ) {F : Stream → Stream}
    (hl : Local F) (hp : Proper F) (hq : Quad F)
    {x y : Stream} (hx : d^[r] x = 0) (hy : EventuallyZero y) :
    polar F x y = 0 := by
  induction r generalizing F x y with
  | zero => change x=0 at hx; rw [hx,polar_zero]
  | succ r ih =>
    have comp := complement_comm hl hq hp
    rw [Function.iterate_succ_apply] at hx
    have e := ih (quotient_local hl comp) (quotient_proper comp hp)
      (quotient_quad comp hq) hx (d_eventual hy)
    rw [polar_semiconj (quotient_semiconj comp)] at e
    exact eventual_d_zero (polar_eventual hl x y hy) e

def localCA {k : ℕ} (f : (Fin k → K) → K) (x : Stream) (i : ℕ) : K :=
    f (fun j => x (i+j.val))

def localPolar {k : ℕ} (f : (Fin k → K) → K) (x y : Fin k → K) : K :=
    f (x+y) + f x + f y + f 0

lemma polar_localCA {k : ℕ} (f : (Fin k → K) → K) (x y : Stream) (i : ℕ) :
    polar (localCA f) x y i = localPolar f (fun j => x (i+j.val)) (fun j => y (i+j.val)) := rfl

theorem no_nonzero_polar {k : ℕ} (f : (Fin k → K) → K)
    (hq : Quad (localCA f)) (hp : Proper (localCA f)) :
    ∀ a b, localPolar f a b = 0 := by
  intro a b
  obtain ⟨e,x,hx,xa⟩ := ext_period_pw a
  let y : Stream := fun i => if h : i<k then b ⟨i,h⟩ else 0
  have hy : EventuallyZero y := ⟨k,fun i hi => by simp [y, show ¬i<k by omega]⟩
  have yb (j : Fin k) : y j.val = b j := by simp [y,j.isLt]
  have hx' := iterate_d_annihilates hx
  have p := iterated_polar_zero (2^e) ⟨k,f,by intros; rfl⟩ hp hq hx' hy
  have h := congrFun p 0
  rw [polar_localCA] at h
  simpa only [Nat.zero_add,xa,yb,Pi.zero_apply] using h

lemma shifted_periodic {n : ℕ} {x : Stream} (h : Periodic n x) (r : ℕ) :
    Periodic (n*r) x := by
  induction r with
  | zero => intro i; rw [Nat.mul_zero,Nat.add_zero]
  | succ r ih =>
    intro i
    rw [Nat.mul_succ,←Nat.add_assoc,h,ih]

lemma periodic_mod {n : ℕ} (_hn : n>0) {x : Stream} (h : Periodic n x) (i : ℕ) :
    x (i%n) = x i := by
  have e := shifted_periodic h (i/n) (i%n)
  simpa only [Nat.mod_add_div] using e.symm

def ringLift {k n : ℕ} (f : (Fin k → K) → K) (x : Fin n → K) (i : Fin n) : K :=
    f (fun j => x ⟨(i.val+j.val)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

lemma proper_of_finite {k : ℕ} (f : (Fin k → K) → K)
    (hp : ∀ n, k ≤ n → Function.Injective (@ringLift k n f)) : Proper (localCA f) := by
  intro n hn x y hx hy eq
  let N := n*(k+1)
  have hN : 0<N := Nat.mul_pos hn (by omega)
  have hNk : k ≤ N := by dsimp [N]; nlinarith
  have PX := shifted_periodic hx (k+1)
  have PY := shifted_periodic hy (k+1)
  let a : Fin N → K := fun i => x i.val
  let b : Fin N → K := fun i => y i.val
  have e : ringLift f a = ringLift f b := by
    ext i
    have ex : ringLift f a i = localCA f x i.val := by
      unfold ringLift localCA; congr 1; ext j; exact periodic_mod hN PX _
    have ey : ringLift f b i = localCA f y i.val := by
      unfold ringLift localCA; congr 1; ext j; exact periodic_mod hN PY _
    rw [ex,ey,eq]
  have h := hp N hNk e
  ext i
  have he := congrFun h (⟨i%N,Nat.mod_lt _ hN⟩ : Fin N)
  change x (i%N) = y (i%N) at he
  rwa [periodic_mod hN PX,periodic_mod hN PY] at he
end QuadraticCA
