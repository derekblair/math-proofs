import RibbonOddResidue
import RibbonIA
import RibbonD3NonstationaryOdd

namespace RibbonD3Odd
open RibbonP11 HaarClass4Structure HaarClass4Ports RibbonDerived3
universe u v

def PrimeBad (p : ℕ) : Prop := p=7 ∨ p=11 ∨ p=13 ∨ p=19 ∨ p=23 ∨ p=29 ∨ p=43
abbrev Triple := RibbonOdd.Triple
abbrev J := RibbonOdd.J
abbrev WideGood := @RibbonD3Mixed3.WideGood

def FieldCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Field K] [Finite K] [Finite G]
      (dnil : DLS G 3=⊥) (x y : G) (μ : G→*Kˣ) (τ : G→K),
    (2:K)≠0 → (3:K)≠0 → Odd (Nat.card G) → IsCocycle μ τ →
    Normalized (RingHom.id K) x y μ τ →
    WideGood x y ∨ ∃ (p : ℕ), PrimeBad p ∧
      ∃ (e : ZMod p→+*K) (a b : ZMod p), e a=(μ x:K) ∧ e b=(μ y:K) ∧ Bad (p,a.val,b.val)

def PairCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (dnil : DLS G 3=⊥) (x y : G)
      (p q : ℕ) (hp : PrimeBad p) (hq : PrimeBad q)
      (μ : G→*(ZMod p)ˣ) (ν : G→*(ZMod q)ˣ) (τ : G→ZMod p) (σ : G→ZMod q),
    Odd (Nat.card G) → IsCocycle μ τ → IsCocycle ν σ →
    Normalized (RingHom.id (ZMod p)) x y μ τ → Normalized (RingHom.id (ZMod q)) x y ν σ →
    Bad (RibbonOdd.Label p μ x y) → Bad (RibbonOdd.Label q ν x y) →
    RibbonOdd.Label p μ x y ≠ RibbonOdd.Label q ν x y → WideGood x y

def JetCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (dnil : DLS G 3=⊥) (x y : G)
      (p : ℕ) (hp : PrimeBad p) (μ : G→*(J p)ˣ) (τ : G→J p),
    Odd (Nat.card G) → IsCocycle μ τ →
    Normalized (TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (ZMod p)).toRingHom x y μ τ →
    Bad (RibbonOdd.JetLabel p μ x y) →
    ((μ x:J p).snd≠0 ∨ (μ y:J p).snd≠0) → WideGood x y

theorem prime_of_bad {p : ℕ} (h : PrimeBad p) : p.Prime := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end RibbonD3Odd
