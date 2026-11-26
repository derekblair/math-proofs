import HaarP3FifthCertData
import HaarP3FifthCertCycle

namespace HaarP3FifthCert
open HaarP3CollectActions HaarAllNoncommuting HaarClass5TemplateClosure HaarUniversal36

variable {G H : Type*} [Group G] [Group H]

def reps (P : Params) : Prop :=
  (0≤P.p ∧ P.p<3) ∧ (0≤P.q ∧ P.q<3) ∧ (0≤P.t0 ∧ P.t0<3) ∧
  (0≤P.t1 ∧ P.t1<3) ∧ (0≤P.t2 ∧ P.t2<3)

theorem coverage_int (P : Params) (r : reps P)
    (he : ¬ (P.p=0 ∧ P.q=0))
    (h12 : ¬ (P.p=1 ∧ P.q=2 ∧ P.t0=2 ∧ P.t1=2 ∧ P.t2=2))
    (h21 : ¬ (P.p=2 ∧ P.q=1 ∧ P.t0=1 ∧ P.t1=1 ∧ P.t2=1)) :
    ∃ C, Valid P C := by
  obtain ⟨a,b,c,d,e⟩ := r
  let f (x : ℤ) (h : 0≤x ∧ x<3) : Fin 3 := ⟨x.toNat,by omega⟩
  have defF (x : ℤ) (h : 0≤x ∧ x<3) : ((f x h).val : ℤ)=x :=
    Int.toNat_of_nonneg h.1
  have nF (x : ℤ) (h : 0≤x ∧ x<3) (n : ℕ) : (f x h).val=n ↔ x=n := by
    constructor
    · intro eq
      have hg := congrArg (fun j : ℕ => (j : ℤ)) eq
      rw [defF x h] at hg
      exact hg
    · intro eq
      apply Int.ofNat_inj.mp
      rw [defF x h,eq]
  have cv := coverage (f P.p a) (f P.q b) (f P.t0 c) (f P.t1 d) (f P.t2 e)
    (by simpa [nF] using he) (by simpa [nF] using h12) (by simpa [nF] using h21)
  simpa only [defF] using cv

theorem conditional (M : Model H) (φ : G →* H) (x y : G)
    (nil : L G 5=⊥) (hx : φ x=M.x) (hy : φ y=M.y)
    (r : reps M.P) (he : ¬ (M.P.p=0 ∧ M.P.q=0))
    (h12 : ¬ (M.P.p=1 ∧ M.P.q=2 ∧ M.P.t0=2 ∧ M.P.t1=2 ∧ M.P.t2=2))
    (h21 : ¬ (M.P.p=2 ∧ M.P.q=1 ∧ M.P.t0=1 ∧ M.P.t1=1 ∧ M.P.t2=1))
    (separates : Separates M) : HasCycle x y 64 := by
  obtain ⟨C,ok⟩ := coverage_int M.P r he h12 h21
  exact lift_cycle M C ok φ x y hx hy (all_closed nil x y C.t) separates

end HaarP3FifthCert
#print axioms HaarP3FifthCert.conditional
