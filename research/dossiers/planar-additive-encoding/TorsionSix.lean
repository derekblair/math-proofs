import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace TorsionSix

abbrev P := ℤ × ℤ

def det (a b c : P) : ℤ :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

def points : Fin 6 → P := ![(6,6),(10,0),(0,0),(0,10),(5,5),(15,0)]

def A (i : Fin 2) : P := points ⟨i.val,by omega⟩
def B (i : Fin 2) : P := points ⟨i.val+2,by omega⟩
def C (i : Fin 2) : P := points ⟨i.val+4,by omega⟩

theorem all_distinct : Function.Injective points := by decide

theorem table (i j k : Fin 2) :
    det (A i) (B j) (C k) = 0 ↔ i=j+k := by decide +revert

theorem only_hits (i j k : Fin 6) (hij : i < j) (hjk : j < k) :
    det (points i) (points j) (points k) = 0 ↔
      (i,j,k)=(0,2,4) ∨ (i,j,k)=(0,3,5) ∨
      (i,j,k)=(1,2,5) ∨ (i,j,k)=(1,3,4) := by decide +revert

theorem no_four (i j k l : Fin 6) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    det (points i) (points j) (points k) ≠ 0 ∨
      det (points i) (points j) (points l) ≠ 0 := by decide +revert

/-- In this instance an exact representation exists precisely in groups
containing nonzero two-torsion. -/
theorem label_iff_two_torsion {G : Type*} [AddCommGroup G] :
    (∃ f g h : Fin 2 → G, ∀ i j k,
      det (A i) (B j) (C k) = 0 ↔ f i+g j+h k=0) ↔
    ∃ t : G, t ≠ 0 ∧ t+t=0 := by
  constructor
  · rintro ⟨f,g,h,e⟩
    let t := f 1-f 0
    refine ⟨t,?_,?_⟩
    · intro z
      have eq : f 1 = f 0 := sub_eq_zero.mp z
      have good : f 0+g 0+h 0=0 := (e 0 0 0).mp (by decide)
      exact (by decide : det (A 1) (B 0) (C 0) ≠ 0)
        ((e 1 0 0).mpr (by simpa [eq] using good))
    · have h0 : f 0+g 0+h 0=0 := (e 0 0 0).mp (by decide)
      have h1 : f 0+g 1+h 1=0 := (e 0 1 1).mp (by decide)
      have h2 : f 1+g 0+h 1=0 := (e 1 0 1).mp (by decide)
      have h3 : f 1+g 1+h 0=0 := (e 1 1 0).mp (by decide)
      calc
        t+t = (f 1+g 0+h 1)+(f 1+g 1+h 0)-
            ((f 0+g 0+h 0)+(f 0+g 1+h 1)) := by dsimp [t]; abel
        _ = 0 := by simp [h0,h1,h2,h3]
  · rintro ⟨t,hn,ht⟩
    refine ⟨![0,t],![0,t],![0,t],?_⟩
    intro i j k
    rw [table]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [ht,hn]

end TorsionSix

#print axioms TorsionSix.no_four
#print axioms TorsionSix.label_iff_two_torsion
