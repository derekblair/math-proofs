import HaarP3Class4Graph
import HaarP3LayerGenBridge

namespace HaarP3Class4Dispatch
open HaarClass4Structure HaarClass4Normal HaarClass4Ports HaarClass4Generate HaarAllNoncommuting HaarP3LayerGen
open HaarP3Class4Cases HaarP3Class4Interpret
variable {G : Type*} [Group G]

def Exceptional (x y : G) : Prop :=
  let f := QuotientGroup.mk' (LS G 4)
  let M := make (ls4quot_class4 G) (f x) (f y)
  orderOf M.a=3 ∧ M.v=M.u^(2:ℕ)*M.a^(2:ℕ) ∧ M.u^(3:ℕ)=1 ∧ M.a^(3:ℕ)=1

theorem dispatch (nil : LS G 5=⊥) (exact5 : LS G 4≠⊥)
    (x y : G) (gen : Generates x y)
    (size : Nat.card ((LS G 2).map (QuotientGroup.mk' (LS G 3)))=3) :
    HasCycle x y 64 ∨ Exceptional x y := by
  let f := QuotientGroup.mk' (LS G 4)
  let nil4 := ls4quot_class4 G
  obtain ⟨_,h⟩ := models_ls4quot exact5 nil x y gen size
  rcases h with ⟨j,t,e,c⟩ | ⟨t,e,c⟩
  · rcases cover (firstAxis j) t e with ⟨w,hw⟩ | ⟨j2,t2,e0⟩
    · exact Or.inl (HaarP3Class4Graph.from_U nil f nil4 x y w j t e c hw)
    · have hj : j=2 := Fin.ext (congrArg (fun i : Fin 4 => i.val) j2)
      subst j
      subst t
      subst e
      obtain ⟨ha,hv,hu,_,_⟩ := c
      exact Or.inr ⟨ha,hv,by convert hu using 1; simp only [show (0 : Fin 3).val=0 by rfl,pow_zero], by rw [←ha,pow_orderOf_eq_one]⟩
  · rcases cover 3 t e with ⟨w,hw⟩ | ⟨h,_,_⟩
    · exact Or.inl (HaarP3Class4Graph.from_V nil f nil4 x y w t e c hw)
    · have hh := congrArg Fin.val h
      norm_num at hh

end HaarP3Class4Dispatch
#print axioms HaarP3Class4Dispatch.dispatch
