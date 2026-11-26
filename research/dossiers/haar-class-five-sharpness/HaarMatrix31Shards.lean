import HaarMatrix31Packed

namespace HaarMatrix31Shards
open HaarMatrix31Packed

structure Seed where
  packed : Array ℕ
  pos : Bool
  last : ℕ
deriving Inhabited

def initial : Seed := ⟨zero,true,3⟩
def advance (s : Seed) (j : ℕ) : Seed := ⟨move s.pos j s.packed,!s.pos,j⟩
def split : ℕ → Seed → List Seed
  | 0,s => [s]
  | n+1,s => [0,1,2].flatMap (fun j => if j=s.last then [] else split n (advance s j))

def tailKeys (k : ℕ) (s : Seed) : List ℕ := words s.packed s.pos s.last k

theorem exact_split (n k : ℕ) (s : Seed) :
    ((split n s).map (tailKeys k)).flatten = tailKeys (n+k) s := by
  induction n generalizing s with
  | zero => simp [split,tailKeys]
  | succ n ih =>
    rw [split, ← List.flatMap_def, List.flatMap_assoc]
    rw [show n+1+k=(n+k)+1 by omega]
    simp only [tailKeys,words]
    congr 1
    funext j
    split
    · rfl
    · exact ih (advance s j)

def shards (n k : ℕ) : List (List ℕ) := (split n initial).map (tailKeys k)

theorem exact_shards (n k : ℕ) : (shards n k).flatten = words zero true 3 (n+k) :=
  exact_split n k initial

end HaarMatrix31Shards
#print axioms HaarMatrix31Shards.exact_shards
