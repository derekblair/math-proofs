import RibbonAsymm

namespace RibbonAsymm

/-- Every pairwise commutator is central in this explicit group. -/
theorem class_two (u v : H) : ∃ w : H, u*v=v*u*w ∧ ∀ h : H, Commute w h := by
  let w : H := ⟨0,0,u.x*v.y-v.x*u.y,0⟩
  refine ⟨w, ?_, ?_⟩
  · change prod u v = prod (prod v u) w
    ext <;> simp [prod, w] <;> ring
  · intro h
    change prod w h=prod h w
    ext <;> simp [prod, w] <;> ring

private theorem root_distinct : ∀ (side : Bool)
    (j k : P), step (side,1) j = step (side,1) k → j=k := by decide +kernel

private theorem no_fixed_root : ∀ (side : Bool) (j : P),
    step (side,1) j ≠ (side,1) := by decide +kernel

theorem loopless (u : V) : ¬ Ribbon.Adj a b u u := by
  intro H
  obtain ⟨p,h⟩ := adj_port H
  obtain ⟨side, g⟩ := u
  apply no_fixed_root side p
  apply left_inj g
  have E : left g (side,1) = (side,g) := by simp [left]
  simpa only [left_step,E] using h

theorem cubic (u : V) : ∃ f : P → V, Function.Injective f ∧
    ∀ v, Ribbon.Adj a b u v ↔ ∃ j, f j=v := by
  refine ⟨step u, ?_, fun v => ⟨adj_port, ?_⟩⟩
  · obtain ⟨side, g⟩ := u
    intro j k eq
    apply root_distinct side j k
    apply left_inj g
    have E : left g (side,1) = (side,g) := by simp [left]
    simpa only [left_step,E] using eq
  · rintro ⟨j,rfl⟩
    exact port_adj _ j

end RibbonAsymm

#print axioms RibbonAsymm.cubic
#print axioms RibbonAsymm.loopless
#print axioms RibbonAsymm.class_two
