import HaarP3LayerGenFifth

namespace HaarP3LayerGen

open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports HaarClass4Data HaarClass4Generate
variable {G : Type*} [Group G]

theorem fifth_gen_cubes (nil : LS G 5=⊥) (x a : G) (ha : a∈LS G 3)
    (hc : a^3∈LS G 4) : ⁅a,x⁆^(3:ℕ)=1 := by
  have hp := Subgroup.mem_center_iff.mp (ls4_center_of_class5 nil (next_layer ha x))
  have hj := Subgroup.mem_center_iff.mp (ls4_center_of_class5 nil hc)
  have h : a*x=x*a*⁅a,x⁆ := right_of_left rfl (fun z => (hp z).symm)
  have e : rc x a=a*⁅a,x⁆ := rc_eq (by simpa only [mul_assoc] using h)
  exact rc_power_central e (fun z => (hp z).symm) 3 (fun z => (hj z).symm)

theorem fifth_all_cubes (nil : LS G 5=⊥) (x y a : G) (gen : Generates x y)
    (ha : a∈LS G 3) (hc : a^3∈LS G 4)
    (span : let f := QuotientGroup.mk' (LS G 4); (LS G 3).map f = Subgroup.zpowers (f a))
    (w : G) (hw : w∈LS G 4) : w^3=1 := by
  let P := ⁅a,x⁆
  let Q := ⁅a,y⁆
  let S := LS G 4
  have hp : P^3=1 := fifth_gen_cubes nil x a ha hc
  have hq : Q^3=1 := fifth_gen_cubes nil y a ha hc
  have e : S=Subgroup.closure ({P,Q} : Set G) := ls4_eq_two_closure nil x y a gen ha span
  change w∈S at hw
  have Z : w∈Subgroup.closure ({P,Q} : Set G) := e ▸ hw
  exact Subgroup.closure_induction (p := fun w _ => w^3=1)
    (fun z hz => by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> assumption)
    (by simp)
    (fun i j hi hj pi pj => by
      have m : i∈S := e.symm ▸ hi
      have c : Commute i j := (Subgroup.mem_center_iff.mp (ls4_center_of_class5 nil m) j).symm
      rw [c.mul_pow,pi,pj,one_mul])
    (fun z hz ih => by rw [inv_pow,ih,inv_one]) Z

end HaarP3LayerGen

#print axioms HaarP3LayerGen.fifth_all_cubes
