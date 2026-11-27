import BalancedExact
import Mathlib.Tactic

namespace WeightedWalk

variable {V : Type*}
variable (E : V → ℤ → V → Prop)

inductive Walk : V → V → List ℤ → Prop
  | nil (x) : Walk x x []
  | step {x y z e L} : E x e y → Walk y z L → Walk x z (e::L)

theorem append {a b c L R} (w : Walk E a b L) (v : Walk E b c R) :
    Walk E a c (L++R) := by
  induction w with
  | nil => exact v
  | step h w ih => exact .step h (ih v)

theorem split {a c L R} (w : Walk E a c (L++R)) :
    ∃ b, Walk E a b L ∧ Walk E b c R := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil a,w⟩
  | cons e L ih =>
    cases w with
    | step h w =>
      obtain ⟨b,p,q⟩ := ih w
      exact ⟨b,.step h p,q⟩

theorem singleton {a b : V} {k : ℤ} (h : Walk E a b [k]) : E a k b := by
  cases h with
  | step edge tail => cases tail; exact edge

theorem unit_letters (hu : ∀ a k b, E a k b → k=1 ∨ k= -1)
    {a b L} (h : Walk E a b L) :
    ∀ k ∈ L, k=1 ∨ k= -1 := by
  induction h with
  | nil => simp
  | step e w ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hmem
    · exact hu _ _ _ e
    · exact ih k hmem

inductive Close : V → V → Prop
  | nil (x) : Close x x
  | join {x y z} : Close x y → Close y z → Close x z
  | pos {x y z w} : E x 1 y → Close y z → E z (-1) w → Close x w
  | neg {x y z w} : E x (-1) y → Close y z → E z 1 w → Close x w

theorem has_zero_walk {a b} (h : Close E a b) :
    ∃ L, Walk E a b L ∧ L.sum=0 := by
  induction h with
  | nil x => exact ⟨[],.nil x,rfl⟩
  | join h₁ h₂ p q =>
    obtain ⟨P,w,hp⟩ := p
    obtain ⟨Q,v,hq⟩ := q
    exact ⟨P++Q,append E w v,by simp [hp,hq]⟩
  | pos e₁ h e₂ ih =>
    obtain ⟨P,w,hp⟩ := ih
    refine ⟨1::(P++[-1]),.step e₁ (append E w (.step e₂ (.nil _))),?_⟩
    simp [hp]
  | neg e₁ h e₂ ih =>
    obtain ⟨P,w,hp⟩ := ih
    refine ⟨(-1)::(P++[1]),.step e₁ (append E w (.step e₂ (.nil _))),?_⟩
    simp [hp]

theorem of_balanced {L} (h : NeutralAffine.Balanced L) :
    ∀ {a b}, Walk E a b L → Close E a b := by
  induction h with
  | nil =>
    intro a b w
    cases w
    exact .nil a
  | append h₁ h₂ p q =>
    intro a b w
    obtain ⟨c,hc,hd⟩ := split E w
    exact .join (p hc) (q hd)
  | pos h ih =>
    intro a b w
    rw [List.append_assoc] at w
    obtain ⟨c,hc,hd⟩ := split E w
    obtain ⟨d,he,hf⟩ := split E hd
    exact .pos (singleton E hc) (ih he) (singleton E hf)
  | neg h ih =>
    intro a b w
    rw [List.append_assoc] at w
    obtain ⟨c,hc,hd⟩ := split E w
    obtain ⟨d,he,hf⟩ := split E hd
    exact .neg (singleton E hc) (ih he) (singleton E hf)

theorem zero_iff_close (hu : ∀ a k b, E a k b → k=1 ∨ k= -1) (a b : V) :
    (∃ L, Walk E a b L ∧ L.sum=0) ↔ Close E a b := by
  constructor
  · rintro ⟨L,w,zero⟩
    exact of_balanced E (BalancedExact.balanced_complete L (unit_letters E hu w) zero) w
  · exact has_zero_walk E

end WeightedWalk

#print axioms WeightedWalk.zero_iff_close
