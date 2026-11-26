import RibbonStationaryChart
import RibbonAffineBase

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (Row Mono pl delta delta_zero eRow zeroRow march run_eval
  prodP prodP_sound poly_eq pl_mul subUV sub_sound avoid_neg rel_from_mul zpow_drop rel_drop
  parametric unit_pow_ok nf mulP mon)
variable {K G : Type*} [Field K] [Group G]

def symbol (k : Count) (i : Nat) : Row :=
  ((spec k).T.take i).foldl march zeroRow

theorem symbol_sound (μ : G →* Kˣ) (τ : G → K) (H : RibbonStationaryChart.Aff μ τ)
    (x y : G) (tx : τ x=0) (ty : τ y=1) (k : Count) (i : Nat) :
    let v := Ribbon5Bridge.pathAt x y (spec k).T.toArray i
    (v.1,μ v.2,τ v.2) = eRow (μ x) (μ y) (symbol k i) :=
  run_eval μ τ H.2 H.1 x y tx ty (Ribbon5Bridge.start G) zeroRow
    (by simp [eRow,pl,zeroRow,Ribbon5Bridge.start,H.1]) _

abbrev Poly := List Mono

def binom (e : Nat) : Poly := [(e,0,1),(0,0,-1)]
def sideA0 : Poly := [(1,0,2),(0,0,1)]
def simple (f : Fin 4) : Poly :=
  ![[(1,0,1),(0,0,-1)],[(1,0,1),(0,0,1)],[(0,1,1),(0,0,1)], sideA0] f

def supported (e : Nat) : Prop := e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=6
instance (e : Nat) : Decidable (supported e) := by unfold supported; infer_instance

def unitCoeff (m : Mono) : Prop := m.2.2=1 ∨ m.2.2=2 ∨ m.2.2= -1 ∨ m.2.2= -2
instance (m : Mono) : Decidable (unitCoeff m) := by unfold unitCoeff; infer_instance

theorem unitCoeff_sound (a b : Kˣ) (two : (2:K)≠0) (m : Mono) (h : unitCoeff m) :
    pl a b [m]≠0 := by
  have J : pl a b [m]=(m.2.2:K)*↑(a^m.1*b^m.2.1) := by simp [pl,mon]
  rw [J]
  apply mul_ne_zero _ (Units.ne_zero _)
  rcases h with e|e|e|e <;> simp [e,two]

theorem supported_dvd (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (e : Nat)
    (hs : supported e) : Nat.Coprime n e := by
  have h2 := odd.coprime_two_right
  have h3 : Nat.Coprime n 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
    exact no3
  rcases hs with rfl|rfl|rfl|rfl|rfl
  · simp
  · exact h2
  · exact h3
  · exact h2.mul_right h2
  · exact h2.mul_right h3

theorem binom_val (a : Kˣ) (e : Nat) : pl a 1 (binom e)= (↑(a^e):K)-1 := by
  simp [pl,binom,mon,sub_eq_add_neg]

theorem root_of_binom (t : Kˣ) (n e : Nat) (odd : Odd n) (no3 : ¬3∣n)
    (tn : t^n=1) (f g : Poly) (he : supported e) (H : nf (mulP f g)=nf (binom e))
    (z : pl t 1 f=0) : t=1 := by
  have J := poly_eq t 1 _ _ H
  rw [pl_mul,z,zero_mul,binom_val] at J
  have E : t^e=1 := Units.ext (sub_eq_zero.mp J.symm)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (supported_dvd n odd no3 e he)
    (orderOf_dvd_iff_pow_eq_one.mpr tn) (orderOf_dvd_iff_pow_eq_one.mpr E))

theorem prod_zero (a b : Kˣ) (m : Mono) (fs : List Poly) (z : pl a b (mulP [m] (prodP fs))=0)
    (h : pl a b [m]≠0) : ∃ f∈fs, pl a b f=0 := by
  rw [pl_mul,prodP_sound] at z
  exact List.mem_map.mp (List.prod_eq_zero_iff.mp ((mul_eq_zero.mp z).resolve_left h))

end RibbonStationaryField
#print axioms RibbonStationaryField.root_of_binom
