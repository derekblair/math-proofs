import Mathlib.Tactic

/-! Exact compressed checks for 16-arm theta witnesses on three bridge-three digons.
Each vertex is encoded by `column * n + sheet`, bridge interiors suppressed.
A bridge has weight three; a digon edge has weight one. -/

namespace BridgeThree
def gain (n : ℕ) (neg : Bool) (j : ℕ) : ℕ :=
  if neg then (1 + n - (j * (n/3)) % n) % n else (1 + j * (n/3)) % n

def rising (n : ℕ) (neg : Bool) (u v : ℕ) : Prop :=
  v/n = u/n + 1 ∧ v < 6*n ∧
  (if (u/n) % 2 = 1 then
    v%n = u%n
   else
    v%n = u%n ∨ v%n = (u%n + gain n neg ((u/n)/2)) % n)

instance (n neg u v) : Decidable (rising n neg u v) := by unfold rising; infer_instance

def edge (n : ℕ) (neg : Bool) (u v : ℕ) : Prop :=
  rising n neg u v ∨ rising n neg v u

instance (n neg u v) : Decidable (edge n neg u v) := by unfold edge; infer_instance

def weight (n u v : ℕ) : ℕ := if min (u/n) (v/n) % 2 = 1 then 3 else 1

def pathWeight (n : ℕ) : List ℕ → ℕ
| x :: y :: t => weight n x y + pathWeight n (y :: t)
| _ => 0

def interior (p : List ℕ) : List ℕ := p.tail.dropLast

def LiteralTheta (n : ℕ) (neg : Bool) (ps : List (List ℕ)) : Prop :=
  ps.length = 3 ∧ ps.head!.head! ≠ ps.head!.getLast! ∧
  ps.all (fun p => decide (p.head! = ps.head!.head! ∧ p.getLast! = ps.head!.getLast! ∧
     p.IsChain (edge n neg) ∧ pathWeight n p = 16)) = true ∧
  (ps.head!.head! :: ps.head!.getLast! :: ps.flatMap interior).Nodup

instance (n neg ps) : Decidable (LiteralTheta n neg ps) := by
  unfold LiteralTheta
  infer_instance

def cert0 : List (List ℕ) := [[9, 8, 17, 26, 30, 39, 48, 41, 32, 19, 28], [9, 0, 10, 1, 11, 2, 12, 3, 13, 4, 14, 5, 15, 24, 28], [9, 18, 31, 40, 49, 42, 51, 44, 53, 37, 28]]
theorem cert0_correct : LiteralTheta 9 false cert0 := by decide
#print axioms cert0_correct

def cert1 : List (List ℕ) := [[9, 0, 10, 19, 35, 26, 33, 24, 15, 5, 14, 4, 13], [9, 8, 17, 7, 16, 25, 32, 23, 30, 21, 12, 3, 13], [9, 18, 27, 36, 49, 40, 31, 22, 13]]
theorem cert1_correct : LiteralTheta 9 true cert1 := by decide
#print axioms cert1_correct

def cert2 : List (List ℕ) := [[27, 0, 28, 1, 29, 56, 83, 73, 100, 63, 36, 8, 35], [27, 26, 53, 25, 52, 24, 51, 78, 88, 61, 34, 7, 35], [27, 54, 81, 108, 135, 116, 89, 62, 35]]
theorem cert2_correct : LiteralTheta 27 false cert2 := by decide
#print axioms cert2_correct

def cert3 : List (List ℕ) := [[27, 0, 28, 1, 29, 2, 30, 3, 31, 4, 32, 5, 33, 6, 34, 7, 35], [27, 26, 53, 25, 52, 24, 51, 78, 97, 70, 89, 62, 35], [27, 54, 100, 73, 92, 65, 38, 10, 37, 9, 36, 8, 35]]
theorem cert3_correct : LiteralTheta 27 true cert3 := by decide
#print axioms cert3_correct

end BridgeThree
