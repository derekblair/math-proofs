import HaarClass6RankOneCert
import HaarClass5TemplateCycles
import HaarClass6RankOneStructure

namespace HaarClass6RankOneClosure
open HaarClass6RankOneCert HaarClass6RankOneStructure
open HaarClass3Table HaarClass3Collector64
open HaarClass5TemplateClosure HaarReducedWalkCycle HaarHalfCollision HaarUniversal36
open scoped commutatorElement
variable {G : Type*} [Group G]
instance (i : ℤ) : Decidable (Range i) := by unfold Range; infer_instance

def AA : List (Fin 3) := [0,1,0,2,1,0,2,1,2,0,1,2]
def dataAA : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,0,0,0,0),(-1,-1,1,-1,-1),(0,-1,1,0,-1),(0,-1,1,0,-1),(0,0,1,0,0),(-1,0,1,-1,0),(-1,1,0,0,1),(-1,1,0,0,1),(0,1,0,0,1),(0,0,0,0,1)]
def rowAA (i : ℕ) : Coord := (dataAA)[i]!
theorem inAA (x y : G) : prodFrom x y 0 AA ∈ L G 2 := by
  refine tail_word x y AA rowAA (by decide) ?_ (by decide)
  suffices e : ∀ i : Fin 12, (label AA i.val=2 → Range (rowAA i.val).1) ∧
      rowAA (i.val+1)=move (decide (i.val%2=0)) (label AA i.val) (rowAA i.val) by
    intro i h
    exact e ⟨i,h⟩
  decide

def AB : List (Fin 3) := [0,1,2,0,1,2,0,1,0,2,1,0,2,0]
def dataAB : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,1,-1,1,0),(-1,1,-1,1,0),(0,1,-1,0,0),(0,0,-1,0,1),(0,0,-1,0,1),(-1,0,-1,1,1),(-1,0,-1,1,1),(-1,-1,0,0,1),(0,-1,0,0,1),(0,-1,0,0,1),(0,0,0,0,1),(0,0,0,0,1)]
def rowAB (i : ℕ) : Coord := (dataAB)[i]!
theorem inAB (x y : G) : prodFrom x y 0 AB ∈ L G 2 := by
  refine tail_word x y AB rowAB (by decide) ?_ (by decide)
  suffices e : ∀ i : Fin 14, (label AB i.val=2 → Range (rowAB i.val).1) ∧
      rowAB (i.val+1)=move (decide (i.val%2=0)) (label AB i.val) (rowAB i.val) by
    intro i h
    exact e ⟨i,h⟩
  decide

def BA : List (Fin 3) := [0,1,0,2,1,0,2,1,2,0,1,2]
def dataBA : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(-1,0,0,0,0),(-1,0,0,0,0),(-1,-1,1,-1,-1),(0,-1,1,0,-1),(0,-1,1,0,-1),(0,0,1,0,0),(-1,0,1,-1,0),(-1,1,0,0,1),(-1,1,0,0,1),(0,1,0,0,1),(0,0,0,0,1)]
def rowBA (i : ℕ) : Coord := (dataBA)[i]!
theorem inBA (x y : G) : prodFrom x y 0 BA ∈ L G 2 := by
  refine tail_word x y BA rowBA (by decide) ?_ (by decide)
  suffices e : ∀ i : Fin 12, (label BA i.val=2 → Range (rowBA i.val).1) ∧
      rowBA (i.val+1)=move (decide (i.val%2=0)) (label BA i.val) (rowBA i.val) by
    intro i h
    exact e ⟨i,h⟩
  decide

def BB : List (Fin 3) := [0,1,2,1,2,0,1,2,0,1,0,2,1,0,1,0]
def BBr : List (Fin 3) := [2,1,2,0,1,2,0,1,0,2,1,0,1,0,0,1]
def dataBB : Array Coord := #[(0,0,0,0,0),(0,1,0,0,0),(-1,1,0,0,0),(-1,2,-1,1,0),(-1,2,-1,1,0),(0,2,-1,0,0),(0,1,-1,0,1),(0,1,-1,0,1),(-1,1,-1,1,1),(-1,1,-1,1,1),(-1,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(1,0,0,0,1),(1,0,0,0,1),(1,0,0,0,1),(0,0,0,0,1)]
def rowBB (i : ℕ) : Coord := (dataBB)[i]!
theorem inBBr (x y : G) : prodFrom x y 0 BBr ∈ L G 2 := by
  refine tail_word x y BBr rowBB (by decide) ?_ (by decide)
  suffices e : ∀ i : Fin 16, (label BBr i.val=2 → Range (rowBB i.val).1) ∧
      rowBB (i.val+1)=move (decide (i.val%2=0)) (label BBr i.val) (rowBB i.val) by
    intro i h
    exact e ⟨i,h⟩
  decide

theorem inBB (x y : G) : prodFrom x y 0 BB ∈ L G 2 := by
  have h : prodFrom x y 0 BB=x⁻¹ * prodFrom x y 0 BBr * (x⁻¹)⁻¹ := by
    norm_num [BB,BBr,prodFrom,signPort,port]
    <;> group
  rw [h]
  exact (inferInstance : (L G 2).Normal).conj_mem _ (inBBr x y) _

def baseW : List (Fin 3) := [0,1,2,0,1,0,2,1,0,2,0,2,1,0,2,1,2,0,1,2,0,1,2,0,1,2,0,1,0,2,1,0,1,2,0,1,2,0,1,0,2,1,2,1,0,2,1,2,0,1,2,0,1,0,1,2,0,1,0,2,1,0,2,1]

set_option maxHeartbeats 2000000 in
theorem base_form (x y : G) : prodFrom x y 0 baseW =
    (y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*y⁻¹*x⁻¹*y*x*y*x⁻¹*y⁻¹*x*y*x⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x) *
      ⁅prodFrom x y 0 AA,prodFrom x y 0 AB⁆ * (y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*y⁻¹*x⁻¹*y*x*y*x⁻¹*y⁻¹*x*y*x⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x)⁻¹ *
    (y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x*y*x⁻¹*y*x⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x*x*y⁻¹*x⁻¹*y⁻¹*x*y*x⁻¹*y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*x⁻¹) *
      ⁅prodFrom x⁻¹ y⁻¹ 0 BA,prodFrom x⁻¹ y⁻¹ 0 BB⁆⁻¹ * (y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x*y*x⁻¹*y*x⁻¹*y⁻¹*x*y⁻¹*x⁻¹*y*x*x*y⁻¹*x⁻¹*y⁻¹*x*y*x⁻¹*y*x⁻¹*y⁻¹*x*y*x⁻¹*y*x*y⁻¹*x⁻¹)⁻¹ := by
  norm_num [baseW,AA,AB,BA,BB,prodFrom,signPort,port,commutatorElement_def]
  <;> group

theorem base_close (nil : L G 6=⊥) (u x y : G)
    (span : let f := QuotientGroup.mk' (L G 3)
      (L G 2).map f = Subgroup.zpowers (f u)) : prodFrom x y 0 baseW=1 := by
  rw [base_form,(gamma3_abelian nil u span (inAA x y) (inAB x y)).commutator_eq,
    (gamma3_abelian nil u span (inBA x⁻¹ y⁻¹) (inBB x⁻¹ y⁻¹)).commutator_eq]
  <;> group

set_option maxHeartbeats 2000000 in
theorem transform0 (x y : G) : prodFrom x y 0 (W 0) =
    (1) * prodFrom (x⁻¹) (y⁻¹) 0 baseW * (1)⁻¹ := by
  norm_num [W,baseW,prodFrom,signPort,port, Matrix.cons_val_zero, Matrix.cons_val_succ]
  <;> group

set_option maxHeartbeats 2000000 in
theorem transform1 (x y : G) : prodFrom x y 0 (W 1) =
    (1) * prodFrom (y⁻¹) (x⁻¹) 0 baseW * (1)⁻¹ := by
  norm_num [W,baseW,prodFrom,signPort,port, Matrix.cons_val_zero, Matrix.cons_val_succ]
  <;> group

set_option maxHeartbeats 2000000 in
theorem transform2 (x y : G) : prodFrom x y 0 (W 2) =
    (x) * prodFrom (y⁻¹*x) (x) 0 baseW * (x)⁻¹ := by
  norm_num [W,baseW,prodFrom,signPort,port, Matrix.cons_val_zero, Matrix.cons_val_succ]
  <;> group

theorem closes (nil : L G 6=⊥) (u x y : G)
    (span : let f := QuotientGroup.mk' (L G 3)
      (L G 2).map f = Subgroup.zpowers (f u)) (w : Fin 3) : prodFrom x y 0 (W w)=1 := by
  fin_cases w
  · change prodFrom x y 0 (W 0)=1
    rw [transform0,base_close nil u _ _ span]
    group
  · change prodFrom x y 0 (W 1)=1
    rw [transform1,base_close nil u _ _ span]
    group
  · change prodFrom x y 0 (W 2)=1
    rw [transform2,base_close nil u _ _ span]
    group

end HaarClass6RankOneClosure
#print axioms HaarClass6RankOneClosure.closes
