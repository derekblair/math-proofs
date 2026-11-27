import HaarDerivedWreathExactClass
import HaarDerivedThree128

namespace HaarDerivedTower
open HaarDerivedWreathCore HaarDerivedWreathExactClass HaarDerivedWreathTrace
open HaarAllNoncommuting
open scoped commutatorElement

theorem raise_nontrivial {Q : Type*} [Group Q] [DecidableEq Q] (d : ℕ)
    (ne : derivedSeries Q d ≠ ⊥) : derivedSeries (W Q) (d+1) ≠ ⊥ := by
  obtain ⟨g,ink,gn⟩ : ∃ g : Q, g ∈ derivedSeries Q d ∧ g≠1 := by
    by_contra! h
    apply ne
    apply bot_unique
    intro g hg
    exact Subgroup.mem_bot.mpr (h g hg)
  let D := derivedSeries (W Q) d
  have hp : purePos g ∈ D :=
    map_derivedSeries_le_derivedSeries purePos d (Subgroup.mem_map_of_mem purePos ink)
  have hD : D.Normal := derivedSeries_normal (W Q) d
  have hd : diffLamp g ∈ D := by
    rw [diffLamp,commutatorElement_def]
    have cc := hD.conj_mem' _ (D.inv_mem hp) lampOne⁻¹
    simpa only [mul_assoc,inv_inv] using D.mul_mem hp cc
  have hw : ⁅purePos g,diffLamp g⁆ ∈ derivedSeries (W Q) (d+1) := by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator hp hd
  intro zero
  rw [zero] at hw
  exact not_commute g gn (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hw))

/-- A finite odd group with cubic Haar ports of ordinary girth 2*h and
derived length exactly d+1. -/
structure Example (h d : ℕ) where
  Q : Type
  [grp : Group Q]
  [fin : Finite Q]
  odd : Odd (Nat.card Q)
  length_lo : derivedSeries Q d ≠ ⊥
  length_hi : derivedSeries Q (d+1)=⊥
  x : Q
  y : Q
  x_ne : x≠1
  y_ne : y≠1
  ne : x≠y
  shortest : HasCycle x y (2*h)
  min_cycle : ∀ n, 3≤n → HasCycle x y n → 2*h≤n
attribute [instance] Example.grp Example.fin

noncomputable def next {h d : ℕ} (E : Example h d) (h3 : 3≤2*h) :
    Example (3*h) (d+1) := by
  classical
  refine ⟨W E.Q,odd_group E.odd,raise_nontrivial d E.length_lo,
    derived_next (d+1) E.length_hi,liftPort E.x E.y 1,liftPort E.x E.y 2, ?_,?_,?_,?_,?_⟩
  · intro e
    exact E.x_ne (congrArg (fun w : W E.Q => w.pos) e)
  · intro e
    exact E.y_ne (congrArg (fun w : W E.Q => w.pos) e)
  · intro e
    exact E.ne (congrArg (fun w : W E.Q => w.pos) e)
  · have a := HaarDerivedWreathUpper.threefold_shortest E.x E.y E.x_ne E.y_ne E.ne
      h h3 E.min_cycle E.shortest
    convert a using 1 <;> omega
  · intro n hn cy
    have e := HaarDerivedWreathGirth.girth_bound E.x E.y E.x_ne E.y_ne E.ne h E.min_cycle n hn cy
    omega

noncomputable def initial : Example 11 1 := by
  open HaarDerivedGirth22 in
  refine ⟨G,odd,?_,length_two,x,y,x_ne_one,y_ne_one,x_ne_y,
    HaarDerivedBase22Witness.cycle22,?_⟩
  · intro e
    rw [derivedSeries_one] at e
    have c : ⁅x,y⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [e] at c
    have xy := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp c)
    have bad : (x*y).left false 0 ≠ (y*x).left false 0 := by decide +kernel
    exact bad (congrArg (fun g : G => g.left false 0) xy)
  · intro n hn cy
    by_contra! small
    exact no_cycle_below22 n hn small cy

/-- Explicit finite odd cubic Haar graph family with exact ordinary girth
22*3^k and underlying groups of exact derived length k+2. -/
noncomputable def examples (k : ℕ) : Example (11*3^k) (k+1) := by
  induction k with
  | zero => exact initial
  | succ k ih =>
    have h3 : 3≤2*(11*3^k) := by
      have p : 0<(3:ℕ)^k := Nat.pow_pos (by decide)
      omega
    have s := next ih h3
    convert s using 1 <;> simp [pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

end HaarDerivedTower
#print axioms HaarDerivedTower.raise_nontrivial
#print axioms HaarDerivedTower.examples
