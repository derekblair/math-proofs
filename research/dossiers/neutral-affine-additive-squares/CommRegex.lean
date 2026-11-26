import SemilinearDecide

namespace CommRegex
open SemilinearWords
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

inductive Expr (G : Type u)
  | empty
  | atom (w : G)
  | alt (a b : Expr G)
  | prod (a b : Expr G)
  | many (a : Expr G)

def image : Expr G → Set G
  | .empty => ∅
  | .atom x => {x}
  | .alt a b => image a ∪ image b
  | .prod a b => {x | ∃ y∈image a, ∃ z∈image b, y+z=x}
  | .many a => AddSubmonoid.closure (image a)

def toSem : Expr G → List (Lin G)
  | .empty => []
  | .atom x => [one x]
  | .alt a b => toSem a ++ toSem b
  | .prod a b => cross (toSem a) (toSem b)
  | .many a => star (toSem a)

theorem toSem_correct (e : Expr G) : sem (toSem e)=image e := by
  induction e with
  | empty => ext; simp [toSem,sem,image]
  | atom x => ext; simp [toSem,sem,image,one_eq]
  | alt a b ha hb =>
    have ex : sem (toSem a ++ toSem b) = sem (toSem a) ∪ sem (toSem b) := by
      ext v
      change (∃ l ∈ toSem a++toSem b, v∈vec l) ↔
        (∃ l∈toSem a, v∈vec l) ∨ (∃ l∈toSem b, v∈vec l)
      simp only [List.mem_append]
      aesop
    simpa only [image,toSem,ha,hb] using ex
  | prod a b ha hb =>
    ext v
    rw [toSem,cross_iff,ha,hb]
    rfl
  | many a ha =>
    ext v
    rw [toSem,star_iff,ha]
    rfl

variable {J : Type*} [Fintype J] [DecidableEq J]

def test (e : Expr (J→ℤ)) (x : J→ℤ) :=
  SemilinearDecide.test (toSem e) x

theorem test_iff (e : Expr (J→ℤ)) (x : J→ℤ) :
    test e x=true ↔ x∈image e := by
  rw [test,SemilinearDecide.test_iff,toSem_correct]

end CommRegex

#print axioms CommRegex.test_iff
