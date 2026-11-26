import HaarOrderTwo
import Mathlib.GroupTheory.OrderOfElement

namespace HaarAllNoncommuting
open HaarCycle
variable {G : Type*} [Group G]

def h (x y : G) := x⁻¹*y
def vk (x y : G) (k : ℕ) (i : Fin (2*k)) : Bool × G :=
  (decide (i.val%2=1), if i.val%2=1 then h x y^(i.val/2)*x⁻¹*y else h x y^(i.val/2)*x⁻¹)

theorem alternate (x y : G) (k : ℕ) [NeZero (2*k)] (hk : orderOf (h x y)=k) (kp : 1<k) :
    ∃ v : Fin (2*k) → Bool × G, Function.Injective v ∧
      ∀ i, haarAdj x y (v i) (v (i+1)) := by
  refine ⟨vk x y k,?_,?_⟩
  · intro i j he
    have ps := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    change decide (i.val%2=1) = decide (j.val%2=1) at ps
    have pa : i.val%2=j.val%2 := by
      by_cases a : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp [a,b] at ps <;> omega
    have pw : h x y^(i.val/2) = h x y^(j.val/2) := by
      by_cases a : i.val%2=1
      · have b : j.val%2=1 := pa.symm.trans a
        simp [vk,a,b] at hs
        exact hs
      · have b : j.val%2≠1 := by omega
        simp [vk,a,b] at hs
        exact hs
    have iL : i.val/2 < orderOf (h x y) := by rw [hk]; omega
    have jL : j.val/2 < orderOf (h x y) := by rw [hk]; omega
    have q := pow_injOn_Iio_orderOf iL jL pw
    apply Fin.ext
    omega
  · intro i
    have I : (i+1).val = (i.val+1)%(2*k) := by
      rw [Fin.val_add]
      have hi : (1 : Fin (2*k)).val = 1 := by
        change 1%(2*k)=1
        exact Nat.mod_eq_of_lt (by omega)
      rw [hi]
    by_cases full : i.val+1<2*k
    · rw [Nat.mod_eq_of_lt full] at I
      by_cases odd : i.val%2=1
      · have ev : ((i+1).val)%2 ≠1 := by omega
        have iq : (i+1).val/2 = i.val/2+1 := by omega
        unfold haarAdj vk
        simp [odd,ev,iq]
        exact Or.inr (Or.inl (by simp [pow_succ,h,mul_assoc]))
      · have od : (i+1).val%2=1 := by omega
        have iq : (i+1).val/2 = i.val/2 := by omega
        unfold haarAdj vk
        simp [odd,od,iq]
    · have eq : i.val+1=2*k := by omega
      rw [eq,Nat.mod_self] at I
      have odd : i.val%2=1 := by omega
      have iq : i.val/2+1=k := by omega
      unfold haarAdj vk
      simp [odd,I]
      have w : h x y^(i.val/2)*x⁻¹*y = 1 := by
        rw [mul_assoc, show x⁻¹*y=h x y by rfl,←pow_succ,iq,←hk,pow_orderOf_eq_one]
      exact Or.inr (Or.inl w)

theorem fourth (x y : G) (xy : x ≠ y) (hh : (x⁻¹*y)^4=1) :
    (∃ v : Fin 4 → Bool × G, Function.Injective v ∧
      ∀ i, haarAdj x y (v i) (v (i+1))) ∨
    (∃ v : Fin 8 → Bool × G, Function.Injective v ∧
      ∀ i, haarAdj x y (v i) (v (i+1))) := by
  let d := orderOf (h x y)
  have dd : d∣4 := orderOf_dvd_of_pow_eq_one hh
  have nne : d≠1 := by
    intro q
    have ev := orderOf_eq_one_iff.mp q
    unfold h at ev
    have e := congrArg (x*·) ev
    apply xy
    simpa [←mul_assoc] using e.symm
  have out : d=2 ∨ d=4 := by
    have q := (Nat.dvd_prime_pow Nat.prime_two (m:=2) (i:=d)).mp dd
    obtain ⟨l,hl,eq⟩ := q
    interval_cases l <;> norm_num at eq <;> tauto
  rcases out with p | p
  · exact Or.inl (alternate x y 2 p (by decide))
  · exact Or.inr (alternate x y 4 p (by decide))

def HasCycle (x y : G) (k : ℕ) : Prop :=
  ∃ v : Fin k → Bool × G, Function.Injective v ∧
    ∀ i, haarAdj x y (v i) (v ⟨(i.val+1)%k,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem cycle_form {x y : G} {k : ℕ} [NeZero k]
    (v : Fin k → Bool × G) (hi : Function.Injective v)
    (ha : ∀ i, haarAdj x y (v i) (v (i+1))) : HasCycle x y k := by
  refine ⟨v,hi,fun i => ?_⟩
  convert ha i using 3
  simp [Fin.val_add,Nat.add_mod_mod]

theorem exists_dyadic (x y z : G) (cx : Commute z x) (cy : Commute z y)
    (rel : x*y=y*x*z) (h1 : z ≠ 1) :
    HasCycle x y 4 ∨ HasCycle x y 8 ∨ HasCycle x y 16 ∨ HasCycle x y 32 := by
  have xy : x ≠ y := by
    rintro rfl
    exact h1 (mul_left_cancel (rel.symm.trans (mul_one _).symm))
  by_cases h2 : z^2=1
  · rcases HaarOrderTwo.choose x y z cx cy rel h1 h2 with ha | hb
    · exact Or.inr (Or.inr (Or.inl (cycle_form _ ha (HaarOrderTwo.adj16 x y z cx cy rel))))
    · rcases fourth x y xy hb with ⟨v,a,b⟩ | ⟨v,a,b⟩
      · exact Or.inl (cycle_form v a b)
      · exact Or.inr (Or.inl (cycle_form v a b))
  · obtain ⟨v,a,b⟩ := commutator_cycle x y z cx cy rel h1 h2
    exact Or.inr (Or.inr (Or.inr (cycle_form v a b)))

end HaarAllNoncommuting
#print axioms HaarAllNoncommuting.exists_dyadic
