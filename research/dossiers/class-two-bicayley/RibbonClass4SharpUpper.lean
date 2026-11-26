import RibbonClass4SharpGraph

namespace RibbonClass4SharpGraph
open scoped commutatorElement
open HaarClass4Structure HaarClass4Ports

def grade : H →* Multiplicative (ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11) where
  toFun g := Multiplicative.ofAdd (g.x,g.y,g.z,g.t)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem low (g : H) (h : g∈LS H 1) : g.x=0 ∧ g.y=0 ∧ g.z=0 ∧ g.t=0 := by
  have H := Abelianization.commutator_subset_ker grade (show g∈commutator H from h)
  change (g.x,g.y,g.z,g.t)=((0:ZMod 11),0,0,0) at H
  simpa using H

private def deep : Subgroup H where
  carrier := {g | g.x=0 ∧ g.y=0 ∧ g.z=0 ∧ g.t=0 ∧ g.u=0 ∧ g.v=0 ∧ g.w=0}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro a b ha hb
    change a.x=0 ∧ a.y=0 ∧ a.z=0 ∧ a.t=0 ∧ a.u=0 ∧ a.v=0 ∧ a.w=0 at ha
    change b.x=0 ∧ b.y=0 ∧ b.z=0 ∧ b.t=0 ∧ b.u=0 ∧ b.v=0 ∧ b.w=0 at hb
    rcases ha with ⟨ha1,ha2,ha3,ha4,ha5,ha6,ha7⟩
    rcases hb with ⟨hb1,hb2,hb3,hb4,hb5,hb6,hb7⟩
    change (prod a b).x=0 ∧ (prod a b).y=0 ∧ (prod a b).z=0 ∧
      (prod a b).t=0 ∧ (prod a b).u=0 ∧ (prod a b).v=0 ∧ (prod a b).w=0
    simp [prod,ha1,ha2,ha3,ha4,ha5,ha6,ha7,hb1,hb2,hb3,hb4,hb5,hb6,hb7]
  inv_mem' := by
    intro a ha
    change a.x=0 ∧ a.y=0 ∧ a.z=0 ∧ a.t=0 ∧ a.u=0 ∧ a.v=0 ∧ a.w=0 at ha
    rcases ha with ⟨ha1,ha2,ha3,ha4,ha5,ha6,ha7⟩
    change (inverse a).x=0 ∧ (inverse a).y=0 ∧ (inverse a).z=0 ∧
      (inverse a).t=0 ∧ (inverse a).u=0 ∧ (inverse a).v=0 ∧ (inverse a).w=0
    simp [inverse,ha1,ha2,ha3,ha4,ha5,ha6,ha7]

set_option maxHeartbeats 1000000 in
private theorem low2 : LS H 2 ≤ deep := by
  change ⁅LS H 1,(⊤ : Subgroup H)⁆ ≤ deep
  apply Subgroup.commutator_le.mpr
  intro g hg h _
  obtain ⟨hx,hy,hz,ht⟩ := low g hg
  change (prod (prod (prod g h) (inverse g)) (inverse h)).x=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).y=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).z=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).t=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).u=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).v=0 ∧
    (prod (prod (prod g h) (inverse g)) (inverse h)).w=0
  simp [prod,inverse,hx,hy,hz,ht]

private def onlyTop (s : ZMod 11) : H := ⟨0,0,0,0,0,0,0,0,0,s⟩

private theorem top_comm (s : ZMod 11) (g : H) : Commute (onlyTop s) g := by
  change prod (onlyTop s) g = prod g (onlyTop s)
  ext <;> simp [prod,onlyTop,add_comm]

private theorem comm_top (g h : H) (G : g∈deep) :
    ⁅g,h⁆ = onlyTop (g.r*h.t-h.x*g.s) := by
  obtain ⟨hx,hy,hz,ht,hu,hv,hw⟩ : g.x=0 ∧ g.y=0 ∧ g.z=0 ∧ g.t=0 ∧
    g.u=0 ∧ g.v=0 ∧ g.w=0 := G
  have H : g*h=onlyTop (g.r*h.t-h.x*g.s)*(h*g) := by
    change prod g h=prod (onlyTop _) (prod h g)
    ext <;> simp [prod,onlyTop,hx,hy,hz,ht,hu,hv,hw] <;> ring
  rw [commutatorElement_def,H]
  group

theorem class_four : LS H 4=⊥ := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr
  change ⁅LS H 2,(⊤ : Subgroup H)⁆ ≤ Subgroup.center H
  apply Subgroup.commutator_le.mpr
  intro g hg h _
  rw [comm_top g h (low2 hg)]
  exact Subgroup.mem_center_iff.mpr (fun k => (top_comm _ k).symm)

def coord : H ≃ ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 ×
    ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 where
  toFun g := (g.x,g.y,g.z,g.t,g.u,g.v,g.w,g.r,g.s,g.f)
  invFun := fun ⟨x,y,z,t,u,v,w,r,s,f⟩ => ⟨x,y,z,t,u,v,w,r,s,f⟩
  left_inv := by intro u; cases u; rfl
  right_inv := by rintro ⟨x,y,z,t,u,v,w,r,s,f⟩; rfl

theorem h_card : Nat.card H = 11^10 := by
  rw [Nat.card_congr coord]
  repeat rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,ZMod.card]
  decide

theorem selected : ⁅portU a b,b⁆ ≠ 1 := by decide +kernel

theorem class_exact : LS H 4=⊥ ∧ LS H 3≠⊥ := by
  refine ⟨class_four,?_⟩
  intro eq
  have T := next_layer (layer_u a b) b
  rw [eq,Subgroup.mem_bot] at T
  exact selected T

theorem cycle32 : Ribbon.Cycle a b 32 := by
  apply RibbonClass4Short.odd_proj_cycle32 class_four (by rw [h_card]; decide)
  intro hc
  have E : RibbonClass4.proj H (portC a b) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  have h := RibbonClass4.target_power_from_proj class_four a b 1 1 (by simpa only [pow_one] using E)
  rw [pow_one] at h
  exact selected h

end RibbonClass4SharpGraph
#print axioms RibbonClass4SharpGraph.class_exact
#print axioms RibbonClass4SharpGraph.cycle32
