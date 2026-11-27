import Mathlib.Tactic

/-! Arithmetic only. Membership in the list of explicit cut-order charts,
before attaching any graph interpretation. -/
namespace SheehanFive

def InteriorChart (a x : Int) : Prop :=
  (x = 1 ∧ x ≤ a - 1) ∨ (2 ≤ x ∧ x ≤ a - 1) ∨
  (x = 1 - a ∧ 2 ≤ a) ∨ (1 - a < x ∧ x ≤ -1)

def EndpointChart (n a b x y : Int) : Prop :=
  (x = 0 ∧ y = -1 ∧ 2 ≤ a) ∨
  (x = 0 ∧ y = b - 1 ∧ 2 ≤ b) ∨
  (x = -a ∧ y = b - 1 ∧ a < b ∧ 2*a+b-1 < n) ∨
  (x = -a ∧ y = b - 1 ∧ b < a ∧ 2 ≤ b ∧ n < 2*a+b-1) ∨
  (a = 1 ∧ x = -1 ∧ y = -1) ∨
  (a = 1 ∧ b = 1 ∧ x = 0 ∧ y = -1) ∨
  (a = 1 ∧ b = 1 ∧ x = -1 ∧ y = 0) ∨
  (a = 1 ∧ b = 1 ∧ x = -a ∧ y = a-1) ∨
  (a = b ∧ 2 ≤ a ∧ 3*a ≤ n ∧ x = -a ∧ y = a-1) ∨
  (a = b ∧ n < 3*a ∧ x = -a ∧ y = a-1)

theorem interiorCover (a x : Int)
    (hL : -a ≤ x) (hR : x ≤ a-1) (hz : x ≠ 0) (ha : x ≠ -a) :
    InteriorChart a x := by
  unfold InteriorChart
  omega

theorem endpointCover (n a b x y : Int) (hn : 5 ≤ n)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hA : 2*a < n) (hB : 2*b < n)
    (hx : x=0 ∨ x= -a) (hy : y= -1 ∨ y=b-1) :
    EndpointChart n a b x y ∨ EndpointChart n b a (-1-y) (-1-x) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · by_cases ha2 : 2 ≤ a
    · exact Or.inl (Or.inl (by omega))
    · by_cases hb2 : 2 ≤ b
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
  · by_cases hb2 : 2 ≤ b
    · exact Or.inl (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
  · by_cases ha2 : 2 ≤ a
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
  · by_cases hEq : a = b
    · by_cases hOne : a = 1
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))
      · by_cases hCut : 3*a ≤ n
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by omega)))))))))))
    · by_cases hLess : a < b
      · by_cases hCut : 2*a+b-1 < n
        · exact Or.inl (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
      · by_cases hCut : 2*b+a-1 < n
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))


theorem signedCover (n a b x y : Int) (hn : 5 ≤ n)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hA : 2*a < n) (hB : 2*b < n)
    (hxL : -a ≤ x) (hxR : x ≤ a-1) (hyL : -b ≤ y) (hyR : y ≤ b-1) :
    InteriorChart a x ∨ InteriorChart b (-1-y) ∨
      EndpointChart n a b x y ∨ EndpointChart n b a (-1-y) (-1-x) := by
  by_cases hx : x=0 ∨ x= -a
  · by_cases hy : y= -1 ∨ y=b-1
    · exact Or.inr (Or.inr (endpointCover n a b x y hn ha hb hA hB hx hy))
    · exact Or.inr (Or.inl (interiorCover b (-1-y) (by omega) (by omega) (by omega) (by omega)))
  · exact Or.inl (interiorCover a x hxL hxR (by omega) (by omega))

theorem centralOrSigned (n a x : Int) (ha : 1 ≤ a)
    (hA : 2*a < n) (hxL : 0 ≤ x) (hxR : x < n) :
    (a ≤ x ∧ x ≤ n-1-a) ∨ (-a ≤ x ∧ x ≤ a-1) ∨
      (-a ≤ x-n ∧ x-n ≤ a-1) := by omega

#print axioms signedCover
#print axioms centralOrSigned
end SheehanFive
