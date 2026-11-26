import HaarDerivedWreathGirth
import HaarVoltageLift

namespace HaarDerivedWreathUpper
open HaarDerivedWreathCore HaarDerivedWreathTrace HaarDerivedWreathGirth
open HaarAllNoncommuting HaarCycle HaarVoltage
open HaarHalfCollision (branch port)
variable {Q : Type*} [Group Q] [DecidableEq Q]

theorem kernel_cube (w : W Q) (hw : w ∈ (π : W Q →* Q).ker) : w^3=1 := by
  have p : w.pos=1 := hw
  have cube : w^3=w*w*w := by rw [pow_succ,pow_two]
  rw [cube]
  apply W.ext'
  · intro b r
    change (mul (mul w w) w).lamp b r = unit.lamp b r
    simp [mul,unit,p,show ∀ q : ZMod 3, q+q+q=0 by decide]
  · change (mul (mul w w) w).pos = unit.pos
    simp [mul,unit,p]

theorem threefold_shortest [Finite Q] (x y : Q) (hx : x≠1) (hy : y≠1) (hxy : x≠y)
    (h : Nat) (n3 : 3≤2*h)
    (lower : ∀ k, 3≤k → HasCycle x y k → 2*h≤k)
    (shortest : HasCycle x y (2*h)) :
    HasCycle (liftPort x y 1) (liftPort x y 2) ((2*h)*3) := by
  let n := 2*h
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨B,inj,adj⟩ := shortest
  have edge (i : Fin n) : haarAdj x y (B i) (B (i+1)) := by
    have I : (⟨(i.val+1)%n,Nat.mod_lt _ (by omega)⟩ : Fin n) = i+1 := by
      apply Fin.ext
      change (i.val+1)%n = (i.val+1%n)%n
      rw [Nat.mod_eq_of_lt (by omega : 1<n)]
    have E := adj i
    change haarAdj x y (B i) (B (⟨(i.val+1)%n,Nat.mod_lt _ (by omega)⟩ : Fin n)) at E
    rwa [I] at E
  classical
  let j (i : Fin n) := Classical.choose (branch x y _ _ (edge i)).2
  have flip (i : Fin n) : (B i).1≠(B (i+1)).1 := by
    have E := (branch x y _ _ (edge i)).1
    cases S : (B i).1 <;> simpa [S] using E
  let s (i : Fin n) := liftPort x y (j i)
  have lab (i : Fin n) : withLabel (liftPort x y 1) (liftPort x y 2) (s i) := by
    dsimp only [withLabel,s]
    generalize j i = c
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  let L (i : Fin n) := stepLabel (B i).1 (s i)
  have stepB (i : Fin n) : (B (i+1)).2=(B i).2*π (L i) := by
    have e := Classical.choose_spec (branch x y _ _ (edge i)).2
    cases S : (B i).1 <;> simpa [L,s,stepLabel,S,basePort,port,j] using e
  let g := pathVal L n
  have hg : g ∈ (π : W Q→*Q).ker := voltage_kernel π B L stepB
  have cube := kernel_cube g hg
  have no : g≠1 := by
    intro eq
    have oneOrd : orderOf g=1 := by rw [eq,orderOf_one]
    have C := HaarVoltageLift.lift_labeled π (liftPort x y 1) (liftPort x y 2)
      B inj s lab flip stepB 1 (by decide) oneOrd
    rw [mul_one] at C
    have bad := girth_bound x y hx hy hxy h lower n n3 C
    omega
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have E : orderOf g=3 := orderOf_eq_prime cube no
  exact HaarVoltageLift.lift_labeled π (liftPort x y 1) (liftPort x y 2)
    B inj s lab flip stepB 3 (by decide) E

end HaarDerivedWreathUpper
#print axioms HaarDerivedWreathUpper.threefold_shortest
