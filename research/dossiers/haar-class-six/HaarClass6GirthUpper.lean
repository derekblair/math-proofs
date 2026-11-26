import HaarClass6ParallelWords
import HaarAnyPorts

namespace HaarClass6GirthUpper
open HaarClass3Table HaarClass3Collector64 HaarClass5TemplateClosure
open HaarReducedWalkCycle HaarAllNoncommuting HaarHalfCollision HaarUniversal36 HaarClass4Ports
open HaarClass6Commute
open scoped commutatorElement
variable {G : Type*} [Group G]

def A : List (Fin 3) := [1,2,0,1,2,0,1,0,2,1,0,2]
def tableA : Array Coord := #[(0,0,0,0,0),(1,0,0,0,0),(1,-1,-1,0,1),(1,-1,-1,0,1),(0,-1,-1,1,1),(0,0,-1,1,0),(0,0,-1,1,0),(1,0,-1,0,0),(1,0,-1,0,0),(1,1,0,0,-1),(0,1,0,0,-1),(0,1,0,0,-1),(0,0,0,0,-1)]
def rowA (i : ℕ) : Coord := tableA[i]!
theorem lenA : A.length=12 := by decide
theorem zeroA : rowA 0=(0,0,0,0,0) := by decide
theorem finalA : rowA 12=(0,0,0,0,-1) := by decide
theorem stepsA (i : Fin 12) :
    (label A i.val=2 → Range (rowA i.val).1) ∧
    rowA (i.val+1)=move (decide (i.val%2=0)) (label A i.val) (rowA i.val) := by
  revert i
  decide +kernel

def B : List (Fin 3) := [0,2,1,2,0,1,2,0,1,0,2,1]
def tableB : Array Coord := #[(0,0,0,0,0),(0,0,0,0,0),(0,-1,0,0,0),(1,-1,0,0,0),(1,-2,-1,0,1),(1,-2,-1,0,1),(0,-2,-1,1,1),(0,-1,-1,1,0),(0,-1,-1,1,0),(1,-1,-1,0,0),(1,-1,-1,0,0),(1,0,0,0,-1),(0,0,0,0,-1)]
def rowB (i : ℕ) : Coord := tableB[i]!
theorem lenB : B.length=12 := by decide
theorem zeroB : rowB 0=(0,0,0,0,0) := by decide
theorem finalB : rowB 12=(0,0,0,0,-1) := by decide
theorem stepsB (i : Fin 12) :
    (label B i.val=2 → Range (rowB i.val).1) ∧
    rowB (i.val+1)=move (decide (i.val%2=0)) (label B i.val) (rowB i.val) := by
  revert i
  decide +kernel

def W : List (Fin 3) := [1,2,0,1,2,0,1,0,2,1,0,2,0,2,1,2,0,1,2,0,1,0,2,1,2,0,1,2,0,1,0,2,0,2,1,0,2,1,2,0]

theorem canonical (x y : G) : prodFrom x y 0 W = ⁅prodFrom x y 0 A,prodFrom x y 0 B⁆ := by
  norm_num [W,A,B,prodFrom,signPort,port,commutatorElement_def]
  group

theorem projected (nil : L G 3=⊥) (x y : G) :
    prodFrom x y 0 A=(portV x y)⁻¹ ∧ prodFrom x y 0 B=(portV x y)⁻¹ := by
  have a := path_matches nil x y A rowA 12 zeroA (fun i h => stepsA ⟨i,h⟩) 12 (by decide)
  have b := path_matches nil x y B rowB 12 zeroB (fun i h => stepsB ⟨i,h⟩) 12 (by decide)
  rw [←lenA,path_full,lenA,finalA] at a
  rw [←lenB,path_full,lenB,finalB] at b
  exact ⟨by simpa [eval,HaarClass3Collect.norm] using a,by simpa [eval,HaarClass3Collect.norm] using b⟩

theorem close (nil : L G 6=⊥) (x y : G) : prodFrom x y 0 W=1 := by
  let a := prodFrom x y 0 A
  let b := prodFrom x y 0 B
  let f := QuotientGroup.mk' (L G 3)
  have ha : a∈L G 2 := by
    apply tail_word x y A rowA zeroA
    · intro i h
      rw [lenA] at h
      exact stepsA ⟨i,h⟩
    · rw [lenA,finalA]; decide
  have t := projected (quote_nil 3) (f x) (f y)
  have eq : f b=f a := by
    change f (prodFrom x y 0 B)=f (prodFrom x y 0 A)
    rw [HaarClass5TemplateClosure.map_prod,HaarClass5TemplateClosure.map_prod,t.1,t.2]
  let z := b*a⁻¹
  have hz : z∈L G 3 := (QuotientGroup.eq_one_iff _).mp (by
    change f (b*a⁻¹)=1
    rw [map_mul,map_inv,eq,mul_inv_cancel])
  have h := central_L2 3 nil hz ha
  have e : b=z*a := by dsimp [z]; group
  rw [canonical]
  change ⁅a,b⁆=1
  rw [e]
  exact (h.symm.mul_right (Commute.refl _)).commutator_eq

theorem normalized (nil : L G 6=⊥) (x y : G) (hx : x≠1) (hy : y≠1) (hxy : x≠y) :
    ∃ k, 4≤k ∧ k≤40 ∧ Even k ∧ HasCycle x y k := by
  have h := HaarReducedWalkCycle.fromWord x y hx hy hxy W (by decide) (by decide) (by decide) (close nil x y)
  exact h

theorem any_ports (nil : L G 6=⊥) (r s t : G) (hr : r≠s) (ht : r≠t) (hs : s≠t) :
    ∃ k, 4≤k ∧ k≤40 ∧ Even k ∧ HaarAnyPorts.HasPortCycle r s t k := by
  obtain ⟨a,b,c⟩ := HaarAnyPorts.as_three r s t hr ht hs
  obtain ⟨k,l,u,e,v⟩ := normalized nil (s*r⁻¹) (t*r⁻¹) a b c
  exact ⟨k,l,u,e,HaarAnyPorts.map_cycle r s t v⟩

end HaarClass6GirthUpper
#print axioms HaarClass6GirthUpper.any_ports
