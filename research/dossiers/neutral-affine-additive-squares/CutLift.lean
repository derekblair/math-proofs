import AffineAddress
import Mathlib.Tactic

namespace CutLift

structure Cut (w : List ℤ) where
  head : List ℤ
  letter : ℤ
  tail : List ℤ
  decomp : w=head++letter::tail

variable {w : List ℤ}

def idx (C : Cut w) : ℕ := C.head.length

theorem pre_eq (C : Cut w) : w.take (idx C) = C.head := by
  calc
    w.take (idx C) = (C.head++C.letter::C.tail).take (idx C) := congrArg (fun l => l.take (idx C)) C.decomp
    _ = _ := by simp [idx,List.take_append]

theorem prefix_succ (C : Cut w) : w.take (idx C+1) = C.head++[C.letter] := by
  calc
    w.take (idx C+1) = (C.head++C.letter::C.tail).take (idx C+1) := congrArg (fun l => l.take (idx C+1)) C.decomp
    _ = _ := by simp [idx,List.take_append]

theorem unique_pos (U V : Cut w) (h : idx U=idx V) : U=V := by
  have e₁ := (pre_eq U).symm.trans ((congrArg (fun i => w.take i) h).trans (pre_eq V))
  have h₁ := (prefix_succ U).symm.trans ((congrArg (fun i => w.take (i+1)) h).trans (prefix_succ V))
  cases U with
  | mk p x q h₀ =>
    cases V with
    | mk p' x' q' h₂ =>
      dsimp at e₁ h₁
      subst p'
      have e₂ : x=x' := by simpa using List.append_right_injective p h₁
      subst x'
      have h₃ := h₀.symm.trans h₂
      have e₃ : q=q' := by simpa using List.append_right_injective p h₃
      subst q'
      rfl

def lift (f : ℤ → List ℤ) (C : Cut w) (D : Cut (f C.letter)) : Cut (w.flatMap f) where
  head := C.head.flatMap f ++ D.head
  letter := D.letter
  tail := D.tail ++ C.tail.flatMap f
  decomp := by
    calc
      w.flatMap f = (C.head++C.letter::C.tail).flatMap f :=
        congrArg (fun l => l.flatMap f) C.decomp
      _ = C.head.flatMap f ++ (f C.letter ++ C.tail.flatMap f) := by rw [List.flatMap_append,List.flatMap_cons]
      _ = C.head.flatMap f ++ ((D.head++D.letter::D.tail) ++ C.tail.flatMap f) :=
        congrArg (fun l => C.head.flatMap f ++ (l++C.tail.flatMap f)) D.decomp
      _ = _ := by simp [List.append_assoc]

theorem lift_idx (f : ℤ → List ℤ) (C : Cut w) (D : Cut (f C.letter)) :
    idx (lift f C D) = (C.head.flatMap f).length+idx D := by
  simp [idx,lift]

theorem unlift (f : ℤ → List ℤ) (C : Cut (w.flatMap f)) :
    ∃ (U : Cut w) (V : Cut (f U.letter)), lift f U V = C := by
  have iu : idx C < (w.flatMap f).length := by
    have := congrArg List.length C.decomp
    simp [idx] at *
    omega
  obtain ⟨a,x,b,r,d,h,e⟩ := AffineAddress.address_exists f w (idx C) iu
  let U : Cut w := ⟨a,x,b,d⟩
  have hpart : ∃ V : Cut (f U.letter), idx V=r := by
    have := AffineAddress.address_exists (fun x : ℤ => [x]) (f x) r (by simpa using h)
    obtain ⟨s,y,t,z,de,lt,eq⟩ := this
    have hz : z=0 := by simp at lt; exact lt
    refine ⟨⟨s,y,t,de⟩,?_⟩
    simpa [hz,idx] using eq.symm
  obtain ⟨V,hV⟩ := hpart
  refine ⟨U,V,unique_pos _ _ ?_⟩
  rw [lift_idx,hV,e]

theorem length_mono (f : ℤ → List ℤ) (u v : List ℤ) (h : u <+: v) :
    (u.flatMap f).length ≤ (v.flatMap f).length := by
  obtain ⟨s,hs⟩ := h
  rw [← hs,List.flatMap_append,List.length_append]
  omega

theorem lift_strict (f : ℤ → List ℤ) (U V : Cut w) (h : idx U < idx V)
    (u : Cut (f U.letter)) (v : Cut (f V.letter)) :
    idx (lift f U u) < idx (lift f V v) := by
  have hP : U.head++[U.letter] <+: V.head := by
    rw [← prefix_succ U,← pre_eq V]
    exact List.take_prefix_take_left (by omega)
  have hh := length_mono f _ _ hP
  rw [List.flatMap_append,List.length_append] at hh
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at hh
  have i : idx u<(f U.letter).length := by
    have := congrArg List.length u.decomp
    simp [idx] at *
    omega
  rw [lift_idx,lift_idx]
  omega

theorem lift_same (f : ℤ → List ℤ) (U : Cut w)
    (u v : Cut (f U.letter)) :
    idx (lift f U u) < idx (lift f U v) ↔ idx u < idx v := by
  simp [lift_idx]

end CutLift

#print axioms CutLift.unlift
#print axioms CutLift.lift_strict
#print axioms CutLift.lift_same
