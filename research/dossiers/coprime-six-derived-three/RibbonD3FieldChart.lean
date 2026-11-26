import RibbonStationaryBezout
import RibbonAffineModCore

namespace RibbonD3Field
open RibbonAffine (Row Mono nf nf_sound eRow march zeroRow pl mon)
open Ribbon5Bridge
variable {K : Type*} [Field K]

abbrev Key := Nat × Nat

structure Label where
  side : Bool
  i : Int
  j : Int
  tr : List Mono
  deriving Inhabited, DecidableEq

def label (r : Row) : Label := ⟨r.side,r.i,r.j,nf r.tr⟩
def Label.toRow (r : Label) : Row := ⟨r.side,r.i,r.j,r.tr⟩
theorem label_eval (a b : Kˣ) (r : Row) : eRow a b (label r).toRow=eRow a b r := by
  simp [label, Label.toRow, eRow, nf_sound]

structure Chart where
  key : Key
  start : Bool
  ports : List P
  reps : Array Label
  map : Array Nat
  deriving Inhabited

def raw (C : Chart) (i : Nat) : Row :=
  (C.ports.take i).foldl march {zeroRow with side := C.start}

def Shape (C : Chart) : Prop :=
  C.ports.length=128 ∧ C.map.size=128 ∧
    ∀ i : Fin 128, C.map[i.val]! < C.reps.size ∧ C.reps[C.map[i.val]!]! = label (raw C i.val)
instance (C : Chart) : Decidable (Shape C) := by unfold Shape; infer_instance

def Ordered (C : Chart) (a b : Kˣ) : Prop :=
  ∀ i j : Fin C.reps.size, i.val<j.val → eRow a b C.reps[i].toRow ≠ eRow a b C.reps[j].toRow

def Separates (C : Chart) (a b : Kˣ) : Prop :=
  ∀ i j : Fin 128, eRow a b (raw C i.val) = eRow a b (raw C j.val) →
    label (raw C i.val) = label (raw C j.val)

theorem separate (C : Chart) (S : Shape C) (a b : Kˣ) (h : Ordered C a b) :
    Separates C a b := by
  intro i j eq
  obtain ⟨hi,ei⟩ := S.2.2 i
  obtain ⟨hj,ej⟩ := S.2.2 j
  let I : Fin C.reps.size := ⟨C.map[i.val]!,hi⟩
  let J : Fin C.reps.size := ⟨C.map[j.val]!,hj⟩
  have Ei : C.reps[I] = label (raw C i.val) := by
    simpa only [I,Fin.getElem_fin,getElem!_pos C.reps (C.map[i.val]!) hi] using ei
  have Ej : C.reps[J] = label (raw C j.val) := by
    simpa only [J,Fin.getElem_fin,getElem!_pos C.reps (C.map[j.val]!) hj] using ej
  have E : eRow a b C.reps[I].toRow=eRow a b C.reps[J].toRow := by rwa [Ei,Ej,label_eval,label_eval]
  by_cases H : I.val=J.val
  · rw [←Ei,←Ej]
    exact congrArg (fun k : Fin C.reps.size => C.reps[k]) (Fin.ext H)
  · rcases lt_or_gt_of_ne H with L|L
    · exact False.elim (h I J L E)
    · exact False.elim (h J I L E.symm)

theorem position_sound {G : Type*} [Group G] (μ : G→*Kˣ) (τ : G→K)
    (co : RibbonStationaryChart.Aff μ τ) (x y : G) (tx : τ x=0) (ty : τ y=1)
    (C : Chart) (i : Nat) :
    let z := run x y (C.start,1) (C.ports.take i)
    (z.1,μ z.2,τ z.2) = eRow (μ x) (μ y) (raw C i) :=
  RibbonAffine.run_eval μ τ co.2 co.1 x y tx ty (C.start,1) {zeroRow with side:=C.start}
    (by simp [zeroRow,eRow,co.1,pl]) _

end RibbonD3Field
#print axioms RibbonD3Field.separate
