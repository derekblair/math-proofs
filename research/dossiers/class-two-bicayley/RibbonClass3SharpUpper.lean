import RibbonClass3SharpGraph

namespace RibbonClass3SharpGraph
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports

def grade : H →* Multiplicative (ZMod 11 × ZMod 11 × ZMod 11) where
  toFun g := Multiplicative.ofAdd (g.x,g.y,g.z)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem low (g : H) (h : g∈LS H 1) : g.x=0 ∧ g.y=0 ∧ g.z=0 := by
  have H := Abelianization.commutator_subset_ker grade (show g∈commutator H from h)
  change (g.x,g.y,g.z)=((0:ZMod 11),0,0) at H
  simpa using H

private def onlyTop (s : ZMod 11) : H := ⟨0,0,0,0,0,s⟩

private theorem top_comm (s : ZMod 11) (g : H) : Commute (onlyTop s) g := by
  change prod (onlyTop s) g = prod g (onlyTop s)
  ext <;> simp [prod,onlyTop,add_comm]

private theorem comm_top (g h : H) (hx : g.x=0) (hy : g.y=0) (hz : g.z=0) :
    ⁅g,h⁆ = onlyTop (g.u*h.z-h.x*g.v) := by
  have H : g*h=onlyTop (g.u*h.z-h.x*g.v)*(h*g) := by
    change prod g h=prod (onlyTop _) (prod h g)
    ext <;> simp [prod,onlyTop,hx,hy,hz] <;> ring
  rw [commutatorElement_def,H]
  group

theorem class_three : LS H 3=⊥ := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr
  change ⁅LS H 1,(⊤ : Subgroup H)⁆ ≤ Subgroup.center H
  apply Subgroup.commutator_le.mpr
  intro g hg h _
  obtain ⟨hx,hy,hz⟩ := low g hg
  rw [comm_top g h hx hy hz]
  exact Subgroup.mem_center_iff.mpr (fun k => (top_comm _ k).symm)

def coord : H ≃ ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 where
  toFun g := (g.x,g.y,g.z,g.u,g.v,g.w)
  invFun g := ⟨g.1,g.2.1,g.2.2.1,g.2.2.2.1,g.2.2.2.2.1,g.2.2.2.2.2⟩
  left_inv := by intro u; cases u; rfl
  right_inv := by rintro ⟨v,w,x,y,z,t⟩; rfl

theorem h_card : Nat.card H = 11^6 := by
  rw [Nat.card_congr coord]
  repeat rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,ZMod.card]
  decide

theorem picked : portV a b≠1 := by decide +kernel

theorem cycle32 : Ribbon.Cycle a b 32 :=
  RibbonClass3.cycle32 a b class_three (by rw [h_card]; decide) false picked

end RibbonClass3SharpGraph
#print axioms RibbonClass3SharpGraph.cycle32
