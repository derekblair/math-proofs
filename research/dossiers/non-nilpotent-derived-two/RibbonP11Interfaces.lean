import RibbonP11Projection
import RibbonDerivedTwoClose
import RibbonP3Odd

namespace RibbonP11
open RibbonAffine HaarClass4Structure HaarClass4Generate HaarClass4Ports
universe u v

abbrev F := ZMod 11

instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev J := TrivSqZeroExt F F

def Normalized {G R K : Type*} [Group G] [CommRing R] [CommRing K]
    (f : R→+*K) (x y : G) (μ : G→*Rˣ) (τ : G→R) : Prop :=
  (f (μ x:R)≠1 ∧ τ x=0 ∧ τ y=1) ∨
  (f (μ x:R)=1 ∧ f (μ y:R)≠1 ∧ τ x=1 ∧ τ y=0)

abbrev Good {G : Type*} [Group G] (x y : G) := RibbonP3.Good x y

/-- Field chart runs either prove the bound or report an exact listed bad pair. -/
def FieldCover (Bad : F×F→Prop) : Prop :=
  ∀ {G : Type u} {K : Type v} [Group G] [Field K] [Finite K] [Finite G]
      (D2 : RibbonDerivedTwo.D2 G) (x y : G)
      (μ : G→*Kˣ) (τ : G→K),
    (2:K)≠0 → Odd (Nat.card G) → (¬3 ∣ Nat.card G) → IsCocycle μ τ →
    Normalized (RingHom.id K) x y μ τ →
    Good x y ∨ ∃ (e : F→+*K) (a b : F), e a=(μ x:K) ∧ e b=(μ y:K) ∧ Bad (a,b)

def PairCover (Bad : F×F→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (D2 : RibbonDerivedTwo.D2 G) (x y : G)
      (μ ν : G→*Fˣ) (τ σ : G→F),
    Odd (Nat.card G) → IsCocycle μ τ → IsCocycle ν σ →
    Normalized (RingHom.id F) x y μ τ → Normalized (RingHom.id F) x y ν σ →
    Bad ((μ x:F),(μ y:F)) → Bad ((ν x:F),(ν y:F)) →
    ((μ x:F),(μ y:F)) ≠ ((ν x:F),(ν y:F)) → Good x y

def JetCover (Bad : F×F→Prop) : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (D2 : RibbonDerivedTwo.D2 G) (x y : G)
      (μ : G→*Jˣ) (τ : G→J),
    Odd (Nat.card G) → IsCocycle μ τ →
    Normalized (TrivSqZeroExt.fstHom F F F).toRingHom x y μ τ →
    Bad ((μ x:J).fst,(μ y:J).fst) →
    ((μ x:J).snd≠0 ∨ (μ y:J).snd≠0) → Good x y

def MetaCover : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (m : RibbonMeta.Meta G) (x y : G),
    Odd (Nat.card G) → x≠1 → y≠1 → Good x y

end RibbonP11
