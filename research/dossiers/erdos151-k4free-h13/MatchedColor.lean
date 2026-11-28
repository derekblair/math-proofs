import BalancedReach
import SeymourDensity

open scoped BigOperators
namespace Erdős151.H12

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def matchedArc (m : V ≃ E) (edge : E → Finset V) (v w : V) : Prop :=
  v ≠ w ∧ w ∈ edge (m v)

instance (m : V ≃ E) (edge : E → Finset V) : DecidableRel (matchedArc m edge) :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ b ∈ edge (m a)))

theorem matched_arc_balance (m : V ≃ E) (edge : E → Finset V)
    (mem : ∀ v, v ∈ edge (m v))
    (row : ∀ e, (∑ v : V, if v ∈ edge e then (1:Nat) else 0) = 3)
    (col : ∀ v, (∑ e : E, if v ∈ edge e then (1:Nat) else 0) = 3) :
    ∀ v, (∑ w : V, if matchedArc m edge v w then (1:Nat) else 0) =
      ∑ w : V, if matchedArc m edge w v then (1:Nat) else 0 := by
  classical
  intro v
  have hd (w : V) : (if matchedArc m edge v w then 1 else 0) +
      (if w=v then 1 else 0) = (if w ∈ edge (m v) then (1:Nat) else 0) := by
    by_cases h : w=v
    · subst w; simp [matchedArc,mem v]
    · simp [matchedArc,h,Ne.symm h]
  have hc (w : V) : (if matchedArc m edge w v then 1 else 0) +
      (if w=v then 1 else 0) = (if v ∈ edge (m w) then (1:Nat) else 0) := by
    by_cases h : w=v
    · subst w; simp [matchedArc,mem v]
    · simp [matchedArc,h]
  have hr := Finset.sum_congr (s₁ := Finset.univ) rfl (fun w _ => hd w)
  have ht := Finset.sum_congr (s₁ := Finset.univ) rfl (fun w _ => hc w)
  rw [Finset.sum_add_distrib,row (m v)] at hr
  rw [Finset.sum_add_distrib] at ht
  have equiv : (∑ w : V, if v ∈ edge (m w) then (1:Nat) else 0) =
      ∑ i : E, if v ∈ edge i then (1:Nat) else 0 :=
    Fintype.sum_equiv m _ _ (fun _ => rfl)
  rw [equiv,col v] at ht
  omega

theorem matched_color_from_alternating_root (m : V ≃ E) (edge : E → Finset V)
    (mem : ∀ v, v ∈ edge (m v))
    (row : ∀ e, (∑ v : V, if v ∈ edge e then (1:Nat) else 0) = 3)
    (col : ∀ v, (∑ e : E, if v ∈ edge e then (1:Nat) else 0) = 3)
    (P : V → Prop) (base : V → Bool) (p : V) (hp : P p)
    (weak : ∀ v, ∃ n, Steps (fun a b => matchedArc m edge a b ∨ matchedArc m edge b a) n v p)
    (alternates : ∀ v, P v → ∃ w, matchedArc m edge v w ∧ P w ∧ base v ≠ base w) :
    ∃ c : V → Bool, ∀ e, Mixed c (edge e) := by
  classical
  have rb := balanced_paths_to_root (matchedArc m edge) (matched_arc_balance m edge mem row col) p weak
  obtain ⟨c,hc⟩ := reach_alternating_root (matchedArc m edge) P base alternates
    (fun v => let ⟨n,h⟩ := rb v; ⟨n,p,hp,h⟩)
  refine ⟨c,fun e => ?_⟩
  let v := m.symm e
  have hve : m v = e := m.apply_symm_apply e
  have hv : v ∈ edge e := hve ▸ mem v
  obtain ⟨w,hw,hcw⟩ := hc v
  have hwe : w∈edge e := hve ▸ hw.2
  by_cases hc0 : c v = true
  · have hw0 : c w = false := by
      cases h : c w <;> first | rfl | exact False.elim (hcw (hc0.trans h.symm))
    exact ⟨⟨v,hv,hc0⟩,⟨w,hwe,hw0⟩⟩
  · have hv0 : c v = false := by
      cases hvv : c v
      · rfl
      · exact False.elim (hc0 hvv)
    have hw0 : c w = true := by
      cases h : c w <;> first | rfl | exact False.elim (hcw (hv0.trans h.symm))
    exact ⟨⟨w,hwe,hw0⟩,⟨v,hv,hv0⟩⟩

#print axioms matched_arc_balance
#print axioms matched_color_from_alternating_root
end Erdős151.H12
