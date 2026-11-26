import HaarP3FifthModelBridge
import HaarP3ExceptionalFinish
import HaarP3FifthCertIntegration
import HaarP3TailSeparateQuot

namespace HaarP3FifthDispatch
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Generate HaarP3LayerGen
open HaarP3FifthData HaarP3Char HaarP3FifthCharacter HaarP3FifthModelBridge HaarAllNoncommuting
variable {G : Type*} [Group G]

theorem dispatch (nil : LS G 5=⊥) (deep : LS G 4≠⊥) (x y : G)
    (gen : Generates x y) (E : HaarP3Class4Dispatch.Exceptional x y) :
    HasCycle x y 32 ∨ HasCycle x y 64 := by
  classical
  let S := LS G 4
  let cent : S≤Subgroup.center G := ls4_center_of_class5 nil
  let c := portC x y
  let u := portU x y
  let v := portV x y
  let a := ⁅u,x⁆
  let D := data x y E
  let p : S := ⟨⁅a,x⁆,next_layer (next_layer (layer_u x y) x) x⟩
  let q : S := ⟨⁅a,y⁆,next_layer (next_layer (layer_u x y) x) y⟩
  let t0 : S := ⟨v*u*a,D.h0⟩
  let t1 : S := ⟨u^(3:ℕ),D.h1⟩
  let t2 : S := ⟨⁅u,y⁆*a,D.h2⟩
  obtain ⟨span,cube⟩ := fifth_layer_exceptional nil x y gen E.2
  by_cases yes : HasCycle x y 64
  · exact Or.inr yes
  · apply Or.inl
    have force (χ : S→*C3) (ne : χ≠1) :
        χ q=(χ p)⁻¹ ∧ χ t0=(χ p)⁻¹ ∧ χ t1=(χ p)⁻¹ ∧ χ t2=(χ p)⁻¹ := by
      apply exceptional_digits
      by_contra bad
      obtain ⟨z,hz⟩ := choose_generator χ ne
      have nz : χ z≠1 := by intro eq; rw [eq,digit_zero] at hz; omega
      let N := centralKernel S χ
      let : N.Normal := kernel_normal cent χ
      let π := QuotientGroup.mk' N
      let M := makeModel nil x y E cube χ z hz
      have sep := HaarP3TailSeparate.separates_char nil x y z χ nz D.ordC
        (by rw [D.ordU]) (by rw [D.ordA]) M rfl rfl rfl rfl rfl rfl
      have r : HaarP3FifthCert.reps M.P :=
        ⟨digit_range _,digit_range _,digit_range _,digit_range _,digit_range _⟩
      exact yes (HaarP3FifthCert.conditional M π x y nil rfl rfl r
        (not_both_zero χ ne p q span) (not_or.mp bad).1 (not_or.mp bad).2 sep)
    obtain ⟨eQ,e0,e1,e2,ep,_,_,_⟩ :=
      exception_relations cent cube p q t0 t1 t2 span deep force
    apply HaarP3ExceptionalFinish.exceptional_cycle32 nil x y gen E.2
    exact ⟨congrArg Subtype.val eQ,congrArg Subtype.val e0,
      congrArg Subtype.val e1,congrArg Subtype.val e2,
      fun e => ep (Subtype.ext e)⟩

end HaarP3FifthDispatch
#print axioms HaarP3FifthDispatch.dispatch
