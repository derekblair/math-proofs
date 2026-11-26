import HaarClass5TemplateCycles
import HaarClass6Commute

namespace HaarClass6ParallelWords
open HaarClass3Table HaarClass3Collector64 HaarClass3Collect
open HaarClass5TemplateClosure HaarReducedWalkCycle HaarHalfCollision HaarUniversal36
open HaarClass4Ports HaarClass6Commute
open scoped commutatorElement
variable {G : Type*} [Group G]

instance (i : ℤ) : Decidable (Range i) := by unfold Range; infer_instance

def A : List (Fin 3) := [0,1,0,2,1,0,2,1,2,0,1,2]
def tableA : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,0,0,0,0),(-1,-1,1,-1,-1),(0,-1,1,0,-1),(0,-1,1,0,-1),(0,0,1,0,0),(-1,0,1,-1,0),(-1,1,0,0,1),(-1,1,0,0,1),(0,1,0,0,1),(0,0,0,0,1)]
def rowA (i : ℕ) : Coord := tableA[i]!
theorem lenA : A.length=12 := by decide
theorem zeroA : rowA 0=(0,0,0,0,0) := by decide
theorem finalA : rowA 12=(0,0,0,0,1) := by decide

set_option maxRecDepth 8000 in
theorem stepsA (i : Fin 12) :
    (label A i.val=2 → Range (rowA i.val).1) ∧
    rowA (i.val+1)=move (decide (i.val%2=0)) (label A i.val) (rowA i.val) := by
  revert i
  decide +kernel

def B : List (Fin 3) := [1,0,1,0,2,0,2,1,2,0,1,2,0,2,0,1,0,2,0,1]
def tableB : Array Coord := #[(0,0,0,0,0),(1,0,0,0,0),(1,0,0,0,0),(2,0,0,0,0),(2,0,0,0,0),(2,1,2,1,0),(2,1,2,1,0),(2,2,4,2,2),(1,2,4,-2,2),(1,3,5,-2,6),(1,3,5,-2,6),(2,3,5,3,6),(2,2,3,2,3),(2,2,3,2,3),(2,1,1,1,2),(2,1,1,1,2),(1,1,1,0,2),(1,1,1,0,2),(1,0,0,0,2),(1,0,0,0,2),(0,0,0,0,2)]
def rowB (i : ℕ) : Coord := tableB[i]!
theorem lenB : B.length=20 := by decide
theorem zeroB : rowB 0=(0,0,0,0,0) := by decide
theorem finalB : rowB 20=(0,0,0,0,2) := by decide

set_option maxRecDepth 8000 in
theorem stepsB (i : Fin 20) :
    (label B i.val=2 → Range (rowB i.val).1) ∧
    rowB (i.val+1)=move (decide (i.val%2=0)) (label B i.val) (rowB i.val) := by
  revert i
  decide +kernel

def W : List (Fin 3) := [0,1,0,2,1,0,2,1,2,0,1,2,1,0,1,0,2,0,2,1,2,0,1,2,0,2,0,1,0,2,0,1,2,1,0,2,1,2,0,1,2,0,1,0,1,0,2,0,1,0,2,0,2,1,0,2,1,2,0,2,0,1,0,1]
def tableW : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,0,0,0,0),(-1,-1,1,-1,-1),(0,-1,1,0,-1),(0,-1,1,0,-1),(0,0,1,0,0),(-1,0,1,-1,0),(-1,1,0,0,1),(-1,1,0,0,1),(0,1,0,0,1),(0,0,0,0,1),(1,0,0,0,1),(1,0,0,0,1),(2,0,0,0,1),(2,0,0,0,1),(2,1,2,1,1),(2,1,2,1,1),(2,2,4,2,3),(1,2,4,-2,3),(1,3,5,-2,7),(1,3,5,-2,7),(2,3,5,3,7),(2,2,3,2,4),(2,2,3,2,4),(2,1,1,1,3),(2,1,1,1,3),(1,1,1,0,3),(1,1,1,0,3),(1,0,0,0,3),(1,0,0,0,3),(0,0,0,0,3),(0,1,0,0,3),(-1,1,0,0,3),(-1,1,0,0,3),(-1,0,1,-1,2),(0,0,1,0,2),(0,-1,1,0,1),(0,-1,1,0,1),(-1,-1,1,-1,1),(-1,0,0,0,2),(-1,0,0,0,2),(0,0,0,0,2),(0,0,0,0,2),(1,0,0,0,2),(1,0,0,0,2),(1,1,1,0,2),(1,1,1,0,2),(2,1,1,1,2),(2,1,1,1,2),(2,2,3,2,3),(2,2,3,2,3),(2,3,5,3,6),(1,3,5,-2,6),(1,3,5,-2,6),(1,2,4,-2,2),(2,2,4,2,2),(2,1,2,1,0),(2,1,2,1,0),(2,0,0,0,0),(2,0,0,0,0),(1,0,0,0,0),(1,0,0,0,0),(0,0,0,0,0)]
def rowW (i : ℕ) : Coord := tableW[i]!
theorem lenW : W.length=64 := by decide
theorem zeroW : rowW 0=(0,0,0,0,0) := by decide
theorem finalW : rowW 64=(0,0,0,0,0) := by decide

set_option maxRecDepth 8000 in
theorem stepsW (i : Fin 64) :
    (label W i.val=2 → Range (rowW i.val).1) ∧
    rowW (i.val+1)=move (decide (i.val%2=0)) (label W i.val) (rowW i.val) := by
  revert i
  decide +kernel

theorem concat : W=A++B++A.reverse++B.reverse := by decide
theorem tail_A (x y : G) : prodFrom x y 0 A∈L G 2 := by
  apply tail_word x y A rowA zeroA
  · intro i hi
    rw [lenA] at hi
    exact stepsA ⟨i,hi⟩
  · rw [lenA,finalA]; decide

theorem projected_loop (nil : L G 3=⊥) (x y : G) :
    prodFrom x y 0 A=portV x y ∧ prodFrom x y 0 B=(portV x y)^(2:ℕ) := by
  have a := path_matches nil x y A rowA 12 zeroA (fun i h => stepsA ⟨i,h⟩) 12 (by decide)
  have b := path_matches nil x y B rowB 20 zeroB (fun i h => stepsB ⟨i,h⟩) 20 (by decide)
  rw [←lenA,path_full,lenA,finalA] at a
  rw [←lenB,path_full,lenB,finalB] at b
  exact ⟨by simpa [eval,HaarClass3Collect.norm] using a,by simpa [eval,HaarClass3Collect.norm] using b⟩

theorem close (nil : L G 6=⊥) (x y : G) : prodFrom x y 0 W=1 := by
  let a := prodFrom x y 0 A
  let b := prodFrom x y 0 B
  let f := QuotientGroup.mk' (L G 3)
  have ha : a∈L G 2 := tail_A x y
  have e := projected_loop (quote_nil 3) (f x) (f y)
  have h : f b=(f a)^(2:ℕ) := by
    change f (prodFrom x y 0 B)=(f (prodFrom x y 0 A))^(2:ℕ)
    rw [HaarClass5TemplateClosure.map_prod,HaarClass5TemplateClosure.map_prod,e.1,e.2]
  let z := b*(a^2)⁻¹
  have hz : z∈L G 3 := (QuotientGroup.eq_one_iff _).mp (by
    change f (b*(a^2)⁻¹)=1
    rw [map_mul,map_inv,map_pow,h,mul_inv_cancel])
  have eza : Commute z a := central_L2 3 nil hz ha
  have bza : b=z*a^2 := by dsimp [z]; group
  have ab : Commute a b := by
    rw [bza]
    exact eza.symm.mul_right ((Commute.refl a).pow_right _)
  rw [concat]
  simp only [prod_append,List.length_append,lenA,lenB,List.length_reverse]
  have eh : prodFrom x y (0+12) B=prodFrom x y 0 B :=
    prod_same_sign x y _ _ _ (by decide)
  rw [eh,prod_reverse x y (0+12+20) 0 A (by rw [lenA]),
    prod_reverse x y (0+12+20+12) 0 B (by rw [lenB])]
  exact ab.commutator_eq

end HaarClass6ParallelWords
#print axioms HaarClass6ParallelWords.close
