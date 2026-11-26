import HeawoodAbelian
import HaarSharpHeawoodCover

namespace HeawoodSharpUnified
open HaarOrbitC7Voltage (B next)

abbrev Base := HaarSharpHeawood.Base
abbrev A := HaarSharpHeawood.A

def loc (i : B) : Base := (decide (7 ≤ i.val), (i.val : ZMod 7))
def code (p : Base) : B :=
  ⟨(if p.1 then 7 else 0)+p.2.val, by have h := ZMod.val_lt p.2; split <;> omega⟩
theorem inverse_left : ∀ i, code (loc i)=i := by decide +kernel
theorem inverse_right : ∀ p, loc (code p)=p := by decide +kernel
def baseEquiv : B ≃ Base := ⟨loc,code,inverse_left,inverse_right⟩

def weights (u v : B) : A :=
  if next u 2 = v then HaarSharpHeawood.voltage (loc u) 2 else 0

theorem anti : ∀ u v, weights v u = -weights u v := by decide +kernel
theorem next_ne : ∀ u j, u≠next u j := by decide +kernel
theorem ports : ∀ u j, loc (next u j) = HaarSharpHeawood.next (loc u) j := by decide +kernel
theorem voltage_eq : ∀ u j, weights u (next u j)=HaarSharpHeawood.voltage (loc u) j := by decide +kernel

def coord : B × A ≃ Base × A := Equiv.prodCongr baseEquiv (Equiv.refl A)

theorem adj_iff (x y : B × A) :
    HaarOrbitC7RealCover.Adj weights x y ↔
      ∃ c, coord y=HaarSharpHeawood.liftNext (coord x) c := by
  constructor
  · rintro ⟨_,c,e,h⟩
    refine ⟨c, Prod.ext ?_ ?_⟩
    · change loc y.1 = HaarSharpHeawood.next (loc x.1) c
      rw [← e,ports]
    · change y.2=x.2+HaarSharpHeawood.voltage (loc x.1) c
      rw [← e,voltage_eq] at h
      exact h.symm
  · rintro ⟨c,e⟩
    have b : HaarSharpHeawood.next (loc x.1) c=loc y.1 := (congrArg (fun p : Base × A => p.1) e).symm
    rw [← ports] at b
    have eq : next x.1 c=y.1 := baseEquiv.injective b
    refine ⟨?_,c,eq,?_⟩
    · rw [←eq]; exact next_ne x.1 c
    · rw [←eq,voltage_eq]
      exact (congrArg (fun p : Base × A => p.2) e).symm

theorem cycle_iff (n : ℕ) :
    HaarOrbitC7RealCover.HasCycle weights n ↔ HaarSharpHeawood.VoltageCycle n := by
  constructor
  · rintro ⟨v,hv,he⟩
    exact ⟨coord ∘ v,coord.injective.comp hv,fun i => (adj_iff _ _).mp (he i)⟩
  · rintro ⟨v,hv,he⟩
    refine ⟨coord.symm ∘ v,coord.symm.injective.comp hv,fun i => ?_⟩
    apply (adj_iff _ _).mpr
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using he i

/-- There is a connected 3,346-vertex abelian voltage cover of Heawood
with least dyadic cycle length 32. The graph isomorphism is explicit. -/
theorem sharp :
    HaarOrbitC7RealCover.HasCycle weights 32 ∧
    ¬ HaarOrbitC7RealCover.HasCycle weights 4 ∧
    ¬ HaarOrbitC7RealCover.HasCycle weights 8 ∧
    ¬ HaarOrbitC7RealCover.HasCycle weights 16 := by
  simpa only [cycle_iff] using HaarSharpHeawood.voltage_sharp

end HeawoodSharpUnified
#print axioms HeawoodSharpUnified.sharp
