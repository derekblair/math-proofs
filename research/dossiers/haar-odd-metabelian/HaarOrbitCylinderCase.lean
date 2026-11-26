import HaarOrbitCylinderHaar
import Mathlib.Tactic.Group

namespace HaarOrbitCylinderCase
open HaarOrbitCylinderVoltage HaarOrbitCylinderChecks HaarMetaVoltagePullback HaarAllNoncommuting
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y t : G)

def side (b : B) : Bool := decide (18≤b.val)
def layer (b : B) : Nat := (b.val%18)/3
def tor (b : B) : Nat := b.val%3
def rep (b : B) : G := x^(layer b)*t^(tor b)
def sh (s : S) : G := x^((delta s).1)*t^((delta s).2)
def rep0 (k : Fin 18) : G := x^(k.val/3)*t^(k.val%3)

private theorem fwd : ∀ u : B, ∀ j : Fin 3, u.val<18 → u≠next u j →
    layer (next u j)=layer u+j.val ∧
    tor (next u j)=(tor u+(if j.val=2 then 1 else 0))%3 := by decide +kernel
private theorem flipTab : ∀ b : B, ∀ j : Fin 3, b≠next b j → side (next b j)= !side b := by decide +kernel
private theorem revTab : ∀ b : B, ∀ j : Fin 3, b≠next b j → next (next b j) j=b := by decide +kernel
private theorem uniqTab : ∀ b : B, ∀ j k : Fin 3, b≠next b j → next b j=next b k → j=k := by decide +kernel

private theorem injectTab : ∀ a b : B,
    side a=side b → a.val%18=b.val%18 → a=b := by decide +kernel
private theorem tor_coincide : ∀ a : B, (a.val%18)%3 = tor a := by decide +kernel
private theorem moveSrc : ∀ s : S, ∀ e : E, active s e=true →
    (layer (tv s (src e)) : ℤ)=(delta s).1+(layer (src e) : ℤ) ∧
    tor (tv s (src e))=((delta s).2+tor (src e))%3 := by decide +kernel
private theorem moveDst : ∀ s : S, ∀ e : E, active s e=true →
    (layer (tv s (dst e)) : ℤ)=(delta s).1+(layer (dst e) : ℤ) ∧
    tor (tv s (dst e))=((delta s).2+tor (dst e))%3 := by decide +kernel

def setup (h3 : orderOf (f t)=3) (cy : f y=(f x)^2*f t) (cm : Commute (f x) (f t))
    (inj : Function.Injective (fun a : Fin 18 => f (rep0 x t a))) : Setup f x y B where
  next := next
  side := side
  repr := rep x t
  inj := by
    intro a b E
    apply injectTab a b (congrArg (fun q : Bool × Q => q.1) E)
    let A : Fin 18 := ⟨a.val%18, by omega⟩
    let B : Fin 18 := ⟨b.val%18, by omega⟩
    have h := congrArg (fun q : Bool × Q => q.2) E
    have hh : f (rep0 x t A)=f (rep0 x t B) := by
      simpa only [rep0,A,B,tor_coincide,rep,layer] using h
    exact congrArg Fin.val (inj hh)
  flip := flipTab
  rev := revTab
  unique := uniqTab
  forward := by
    intro b j ne hs
    have lo : b.val<18 := by
      unfold side at hs
      by_contra H
      have nh : 18≤b.val := by omega
      simp [nh] at hs
    obtain ⟨a,c⟩ := fwd b j lo ne
    simp only [rep,map_mul,map_pow,a,c]
    have e := pow_mod_orderOf (f t) (tor b+(if j.val=2 then 1 else 0))
    rw [h3] at e
    rw [e,pow_add,pow_add]
    fin_cases j
    · simp [HaarMetaVoltagePullback.port]
    · simp only [HaarMetaVoltagePullback.port]
      change (f x)^layer b * (f x)^1 * ((f t)^tor b * (f t)^0) =
        (f x)^layer b * (f t)^tor b * f x
      simp only [pow_one,pow_zero,mul_one,mul_assoc]
      rw [(cm.pow_right (tor b)).eq]
    · simp only [HaarMetaVoltagePullback.port]
      change (f x)^layer b * (f x)^2 * ((f t)^tor b * (f t)^1) =
        (f x)^layer b * (f t)^tor b * f y
      rw [cy,pow_one]
      calc
        _ = (f x)^layer b * (((f x)^2 * (f t)^tor b) * f t) := by group
        _ = (f x)^layer b * (((f t)^tor b * (f x)^2) * f t) := by
          rw [((cm.pow_left 2).pow_right (tor b)).eq]
        _ = _ := by group

private theorem movement (h3 : orderOf (f t)=3) (cm : Commute (f x) (f t))
    (s : S) (b : B)
    (a : (layer (tv s b) : ℤ) = (delta s).1 + (layer b : ℤ))
    (c : tor (tv s b) = ((delta s).2+tor b)%3) :
    f (sh x t s * rep x t b)=f (rep x t (tv s b)) := by
  simp only [sh,rep,map_mul,map_pow,map_zpow,c]
  have e := pow_mod_orderOf (f t) ((delta s).2+tor b)
  rw [h3] at e
  rw [e,pow_add]
  have xx : (f x)^layer (tv s b) = (f x)^((delta s).1) * (f x)^layer b := by
    rw [← zpow_natCast (f x) (layer (tv s b)),a,zpow_add,zpow_natCast]
  rw [xx]
  calc
    _ = (f x)^((delta s).1) * (((f t)^((delta s).2) * (f x)^layer b) * (f t)^tor b) := by group
    _ = (f x)^((delta s).1) * (((f x)^layer b * (f t)^((delta s).2)) * (f t)^tor b) := by
      rw [← ((cm.pow_left (layer b)).pow_right (delta s).2).eq]
    _ = _ := by group

theorem rep0_inj_of_relative_order {R : Type*} [Group R] (q : Q →* R)
    (kill : q (f t)=1) (lo : 6≤orderOf (q (f x))) (ht : orderOf (f t)=3) :
    Function.Injective (fun a : Fin 18 => f (rep0 x t a)) := by
  intro a b E
  have eq : (f x)^(a.val/3)*(f t)^(a.val%3) =
      (f x)^(b.val/3)*(f t)^(b.val%3) := by
    simpa only [rep0,map_mul,map_pow] using E
  have h0 := congrArg q eq
  simp only [map_mul,map_pow,kill,one_pow,mul_one] at h0
  have na : a.val/3 ∈ Set.Iio (orderOf (q (f x))) := by
    change a.val/3 < orderOf (q (f x))
    have := a.isLt
    omega
  have nb : b.val/3 ∈ Set.Iio (orderOf (q (f x))) := by
    change b.val/3 < orderOf (q (f x))
    have := b.isLt
    omega
  have lEq : a.val/3=b.val/3 := pow_injOn_Iio_orderOf na nb h0
  rw [lEq] at eq
  have h1 := mul_left_cancel eq
  have ma : a.val%3 ∈ Set.Iio (orderOf (f t)) := by
    change a.val%3 < orderOf (f t)
    rw [ht]
    omega
  have mb : b.val%3 ∈ Set.Iio (orderOf (f t)) := by
    change b.val%3 < orderOf (f t)
    rw [ht]
    omega
  have mEq : a.val%3=b.val%3 := pow_injOn_Iio_orderOf ma mb h1
  apply Fin.ext
  omega

theorem cycle [Finite G] (odd : Odd (Nat.card G))
    [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
    (h3 : orderOf (f t)=3) (cy : f y=(f x)^2*f t) (cm : Commute (f x) (f t))
    (inj : Function.Injective (fun a : Fin 18 => f (rep0 x t a))) :
    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle x y n := by
  let T := setup f x y t h3 cy cm inj
  exact HaarOrbitCylinderHaar.finite_odd T rfl (fun _ => rfl) (sh x t)
    (fun s e he => ⟨movement f x t h3 cm s (src e) (moveSrc s e he).1 (moveSrc s e he).2,
      movement f x t h3 cm s (dst e) (moveDst s e he).1 (moveDst s e he).2⟩) odd

end HaarOrbitCylinderCase
#print axioms HaarOrbitCylinderCase.cycle
