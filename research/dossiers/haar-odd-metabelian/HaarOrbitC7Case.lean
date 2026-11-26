import HaarOrbitC7Haar

namespace HaarOrbitC7Case
open HaarOrbitC7Voltage HaarOrbitC7Checks HaarMetaVoltagePullback HaarOrbitC7Haar HaarAllNoncommuting
variable {G Q : Type*} [Group G] [Group Q]
variable (f : G →* Q) (x y : G)

def side (b : B) : Bool := decide (7≤b.val)
def rep (b : B) : G := x^(b.val%7)
def sh (s : S) : G := x^((delta s).1.toNat)

private theorem forwardTab : ∀ u : B, ∀ j : Fin 3, u.val<7 →
    (next u j).val%7=(u.val%7+(![0,1,3] : Fin 3 → ℕ) j)%7 := by decide +kernel

private theorem flipTab : ∀ b : B, ∀ j : Fin 3, b≠next b j → side (next b j)= !side b := by decide +kernel
private theorem revTab : ∀ b : B, ∀ j : Fin 3, b≠next b j → next (next b j) j=b := by decide +kernel
private theorem uniqTab : ∀ b : B, ∀ j k : Fin 3, b≠next b j → next b j=next b k → j=k := by decide +kernel
private theorem injectTab : ∀ a b : B, side a=side b → a.val%7=b.val%7 → a=b := by decide +kernel
private theorem moveTab : ∀ s : S, ∀ b : B,
    (tv s b).val%7=((delta s).1.toNat+b.val%7)%7 := by decide +kernel

def setup (order : orderOf (f x)=7) (h3 : f y=(f x)^3) : Setup f x y B where
  next := next
  side := side
  repr := rep x
  inj := by
    intro a b E
    apply injectTab a b (congrArg (fun z : Bool × Q => z.1) E)
    have ha : a.val%7 ∈ Set.Iio (orderOf (f x)) := by
      change _ < orderOf (f x)
      rw [order]
      exact Nat.mod_lt _ (by decide)
    have hb : b.val%7 ∈ Set.Iio (orderOf (f x)) := by
      change _ < orderOf (f x)
      rw [order]
      exact Nat.mod_lt _ (by decide)
    have e := congrArg (fun z : Bool × Q => z.2) E
    exact pow_injOn_Iio_orderOf ha hb (by simpa only [rep,map_pow] using e)
  flip := flipTab
  rev := revTab
  unique := uniqTab
  forward := by
    intro b j _ h
    have lo : b.val<7 := by
      unfold side at h
      by_contra H
      have nh : 7≤b.val := by omega
      simp [nh] at h
    simp only [rep,map_pow,forwardTab b j lo]
    have e := pow_mod_orderOf (f x) (b.val%7+(![0,1,3] : Fin 3 → ℕ) j)
    rw [order] at e
    rw [e,pow_add]
    fin_cases j <;> simp [HaarMetaVoltagePullback.port,h3]

private theorem movement (order : orderOf (f x)=7) (s : S) (b : B) :
    f (sh x s * rep x b)=f (rep x (tv s b)) := by
  simp only [sh,rep,map_mul,map_pow,moveTab]
  have e := pow_mod_orderOf (f x) ((delta s).1.toNat+b.val%7)
  rw [order] at e
  rw [e,pow_add]

theorem cycle [Finite G] (odd : Odd (Nat.card G))
    [hc : Fact (∀ (a b : f.ker), a*b=b*a)]
    (order : orderOf (f x)=7) (h3 : f y=(f x)^3) :
    ∃ k, k ∈ [4,8,16,32] ∧ HasCycle x y k := by
  let T := setup f x y order h3
  exact finite_odd T rfl (fun _ => rfl) (sh x) (fun s e _ =>
    ⟨movement f x order s (src e),movement f x order s (dst e)⟩) odd

end HaarOrbitC7Case
#print axioms HaarOrbitC7Case.cycle
