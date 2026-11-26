import HaarClass6RankTwoCert
import HaarClass5TemplateCycles

namespace HaarThirdAbelianRankTwoClosure
open HaarClass6RankTwoCert
open HaarClass3Table HaarClass3Collector64
open HaarClass5TemplateClosure HaarReducedWalkCycle HaarHalfCollision HaarUniversal36
open HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]
instance (i : ℤ) : Decidable (Range i) := by unfold Range; infer_instance

def A : Fin 3 → List (Fin 3) := ![[0,1,2,0,1,2,0,2,1,0,2,1],[0,1,2,0,1,2,1,0,2,1,0,2],[0,2,1,0,2,1,0,1,2,0,1,2]]
def tableA : Fin 3 → Array Coord := ![#[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,1,-1,1,0),(-1,1,-1,1,0),(0,1,-1,0,0),(0,0,-1,0,1),(0,0,-1,0,1),(0,-1,-1,0,2),(1,-1,-1,-1,2),(1,-1,-1,-1,2),(1,0,0,-1,1),(0,0,0,-1,1)],#[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,1,-1,1,0),(-1,1,-1,1,0),(0,1,-1,0,0),(0,0,-1,0,1),(1,0,-1,-1,1),(1,0,-1,-1,1),(1,1,0,-1,0),(0,1,0,-1,0),(0,1,0,-1,0),(0,0,0,-1,0)],#[(0,0,0,0,0),(0,0,0,0,0),(0,-1,0,0,0),(1,-1,0,0,0),(1,-1,0,0,0),(1,0,1,0,0),(0,0,1,-1,0),(0,0,1,-1,0),(-1,0,1,-2,0),(-1,1,0,-1,1),(-1,1,0,-1,1),(0,1,0,-1,1),(0,0,0,-1,1)]]
def rowA (t : Fin 3) (i : ℕ) : Coord := (tableA t)[i]!
theorem lenA (t : Fin 3) : (A t).length=12 := by revert t; decide
theorem zeroA (t : Fin 3) : rowA t 0=(0,0,0,0,0) := by revert t; decide
theorem stepsA (t : Fin 3) (i : Fin 12) :
    (label (A t) i.val=2 → Range (rowA t i.val).1) ∧
    rowA t (i.val+1)=move (decide (i.val%2=0)) (label (A t) i.val) (rowA t i.val) := by
  revert t i
  decide

def B : Fin 3 → List (Fin 3) := ![[2,0,1,2,0,1,2,0,1,2,0,2,1,0,2,1,2,1,0,2],[1,0,2,1,0,1,2,0,1,2,1,0,2,1,0,2,1,2,0,1],[1,0,2,1,0,2,1,0,2,1,0,1,2,0,1,2,1,2,0,1]]
def tableB : Fin 3 → Array Coord := ![#[(0,0,0,0,0),(0,1,0,0,0),(0,1,0,0,0),(1,1,0,0,0),(1,0,-1,0,1),(1,0,-1,0,1),(0,0,-1,1,1),(0,1,-1,1,0),(0,1,-1,1,0),(1,1,-1,0,0),(1,0,-2,0,2),(1,0,-2,0,2),(1,-1,-3,0,5),(2,-1,-3,-3,5),(2,-1,-3,-3,5),(2,0,-1,-2,2),(1,0,-1,-1,2),(1,1,0,-1,1),(0,1,0,-1,1),(0,1,0,-1,1),(0,0,0,-1,1)],#[(0,0,0,0,0),(1,0,0,0,0),(1,0,0,0,0),(1,1,1,0,0),(0,1,1,-1,0),(0,1,1,-1,0),(-1,1,1,-2,0),(-1,2,0,-1,1),(-1,2,0,-1,1),(0,2,0,-1,1),(0,1,0,-1,1),(1,1,0,-1,1),(1,1,0,-1,1),(1,2,1,-1,1),(0,2,1,-2,1),(0,2,1,-2,1),(0,1,1,-2,0),(1,1,1,-1,0),(1,0,0,-1,0),(1,0,0,-1,0),(0,0,0,-1,0)],#[(0,0,0,0,0),(1,0,0,0,0),(1,0,0,0,0),(1,1,1,0,0),(0,1,1,-1,0),(0,1,1,-1,0),(0,0,1,-1,-1),(1,0,1,0,-1),(1,0,1,0,-1),(1,1,2,0,0),(0,1,2,-2,0),(0,1,2,-2,0),(-1,1,2,-4,0),(-1,2,1,-3,2),(-1,2,1,-3,2),(0,2,1,-2,2),(0,1,1,-2,1),(1,1,1,-1,1),(1,0,0,-1,1),(1,0,0,-1,1),(0,0,0,-1,1)]]
def rowB (t : Fin 3) (i : ℕ) : Coord := (tableB t)[i]!
theorem lenB (t : Fin 3) : (B t).length=20 := by revert t; decide
theorem zeroB (t : Fin 3) : rowB t 0=(0,0,0,0,0) := by revert t; decide
theorem stepsB (t : Fin 3) (i : Fin 20) :
    (label (B t) i.val=2 → Range (rowB t i.val).1) ∧
    rowB t (i.val+1)=move (decide (i.val%2=0)) (label (B t) i.val) (rowB t i.val) := by
  revert t i
  decide

theorem concat (t : Fin 3) : W t=A t++B t++(A t).reverse++(B t).reverse := by revert t; decide
theorem final_eq (t : Fin 3) : rowA t 12 = rowB t 20 := by revert t; decide
theorem grade (t : Fin 3) : (rowA t 12).1=0 ∧ (rowA t 12).2.1=0 ∧
    (rowA t 12).2.2.1=0 := by revert t; decide

theorem A_in (x y : G) (t : Fin 3) : prodFrom x y 0 (A t) ∈ L G 2 := by
  apply tail_word x y (A t) (rowA t) (zeroA t)
  · intro i hi
    rw [lenA] at hi
    exact stepsA t ⟨i,hi⟩
  · rw [lenA]; exact grade t

theorem projected_equal (cls : L G 3=⊥) (x y : G) (t : Fin 3) :
    prodFrom x y 0 (A t)=prodFrom x y 0 (B t) := by
  have a := path_matches cls x y (A t) (rowA t) 12 (zeroA t) (fun i h => stepsA t ⟨i,h⟩) 12 (by decide)
  have b := path_matches cls x y (B t) (rowB t) 20 (zeroB t) (fun i h => stepsB t ⟨i,h⟩) 20 (by decide)
  rw [←lenA t,path_full,lenA t,final_eq t] at a
  rw [←lenB t,path_full,lenB t] at b
  exact a.trans b.symm

theorem closes
    (abel : ∀ a b : G, a ∈ L G 2 → b ∈ L G 2 → Commute a b) (x y : G) (t : Fin 3) : prodFrom x y 0 (W t)=1 := by
  let a := prodFrom x y 0 (A t)
  let b := prodFrom x y 0 (B t)
  let f := QuotientGroup.mk' (L G 3)
  have ha : a∈L G 2 := A_in x y t
  have h : f b=f a := by
    change f (prodFrom x y 0 (B t))=f (prodFrom x y 0 (A t))
    rw [HaarClass5TemplateClosure.map_prod,HaarClass5TemplateClosure.map_prod]
    exact (projected_equal (quote_nil 3) (f x) (f y) t).symm
  let z := b*a⁻¹
  have hz : z∈L G 3 := (QuotientGroup.eq_one_iff _).mp (by
    change f (b*a⁻¹)=1
    rw [map_mul,map_inv,h,mul_inv_cancel])
  have in2 : z ∈ L G 2 :=
    (Subgroup.lowerCentralSeries_antitone _ (by decide : 2≤3)) hz
  have eza := abel z a in2 ha
  have bza : b=z*a := by dsimp [z]; group
  have ab : Commute a b := by
    rw [bza]
    exact eza.symm.mul_right (Commute.refl a)
  rw [concat]
  simp only [prod_append,List.length_append,lenA,lenB,List.length_reverse]
  have eh : prodFrom x y (0+12) (B t)=prodFrom x y 0 (B t) :=
    prod_same_sign x y _ _ _ (by decide)
  rw [eh,prod_reverse x y (0+12+20) 0 (A t) (by rw [lenA]),
    prod_reverse x y (0+12+20+12) 0 (B t) (by rw [lenB])]
  exact ab.commutator_eq

end HaarThirdAbelianRankTwoClosure
#print axioms HaarThirdAbelianRankTwoClosure.closes
