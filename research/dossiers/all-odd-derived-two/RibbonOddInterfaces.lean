import RibbonP11Stationary

namespace RibbonOdd
open RibbonP11 HaarClass4Structure HaarClass4Ports
universe u v

def PrimeBad (p : ℕ) : Prop := p=7 ∨ p=11 ∨ p=13
abbrev Triple := ℕ × ℕ × ℕ
abbrev J (p : ℕ) := TrivSqZeroExt (ZMod p) (ZMod p)
def Label {G : Type*} [Group G] (p : ℕ) (μ : G→*(ZMod p)ˣ) (x y : G) : Triple :=
  (p,(μ x : ZMod p).val,(μ y : ZMod p).val)
def JetLabel {G : Type*} [Group G] (p : ℕ) (μ : G→*(J p)ˣ) (x y : G) : Triple :=
  (p,(μ x : J p).fst.val,(μ y : J p).fst.val)

def FieldCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Field K] [Finite K] [Finite G]
      (D2 : RibbonDerivedTwo.D2 G) (x y : G) (μ : G→*Kˣ) (τ : G→K),
    (2:K)≠0 → Odd (Nat.card G) → IsCocycle μ τ →
    Normalized (RingHom.id K) x y μ τ →
    Good x y ∨ ∃ (p : ℕ), PrimeBad p ∧
      ∃ (e : ZMod p→+*K) (a b : ZMod p), e a=(μ x:K) ∧ e b=(μ y:K) ∧ Bad (p,a.val,b.val)

def PairCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (D2 : RibbonDerivedTwo.D2 G) (x y : G)
      (p q : ℕ) (hp : PrimeBad p) (hq : PrimeBad q)
      (μ : G→*(ZMod p)ˣ) (ν : G→*(ZMod q)ˣ) (τ : G→ZMod p) (σ : G→ZMod q),
    Odd (Nat.card G) → IsCocycle μ τ → IsCocycle ν σ →
    Normalized (RingHom.id (ZMod p)) x y μ τ → Normalized (RingHom.id (ZMod q)) x y ν σ →
    Bad (Label p μ x y) → Bad (Label q ν x y) →
    Label p μ x y ≠ Label q ν x y → Good x y

def JetCover (Bad : Triple→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (D2 : RibbonDerivedTwo.D2 G) (x y : G)
      (p : ℕ) (hp : PrimeBad p) (μ : G→*(J p)ˣ) (τ : G→J p),
    Odd (Nat.card G) → IsCocycle μ τ →
    Normalized (TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (ZMod p)).toRingHom x y μ τ →
    Bad (JetLabel p μ x y) →
    ((μ x:J p).snd≠0 ∨ (μ y:J p).snd≠0) → Good x y

theorem prime_of_bad {p : ℕ} (h : PrimeBad p) : p.Prime := by
  rcases h with rfl | rfl | rfl <;> decide

end RibbonOdd
