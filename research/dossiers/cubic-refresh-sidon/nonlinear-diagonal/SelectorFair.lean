import Lean.Elab.Tactic.Omega
namespace SelectorFair

theorem complement_count {T : Type} (p : T → Bool) (xs : List T) :
    xs.countP p + xs.countP (fun x => !p x)=xs.length := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    cases h : p a <;> simp [List.countP_cons,h] at * <;> omega

/-- Selecting a uniform site from a balanced list remains fair after
    XOR with the membership bit of one fixed distinguished site. -/
theorem xor_balanced {T : Type} (p : T → Bool) (xs : List T) (fixed : Bool)
    (balance : 2*xs.countP p=xs.length) :
    2*xs.countP (fun x => p x != fixed)=xs.length := by
  cases fixed
  · have E : (fun x => p x != false)=p := by
      funext x
      cases p x <;> rfl
    rwa [E]
  · have hh := complement_count p xs
    have E : (fun x => p x != true)=(fun x => !p x) := by
      funext x
      cases p x <;> rfl
    rw [E]
    omega

end SelectorFair
#print axioms SelectorFair.xor_balanced
