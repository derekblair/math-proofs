import RibbonD3FieldBase
import RibbonD3FieldCharts
import RibbonStationarySurfaceCore

namespace RibbonD3Field
open RibbonAffine (eRow pl mon nf delta delta_zero mulP prodP prodP_sound poly_eq pl_mul pl_append)
open RibbonStationaryField (Poly Id natConst surfaceBinom id_sound_surface multiplier_zero
  Specialization coprime_drop binom_val)
variable {K : Type*} [Field K]

/-- Bivariate elimination using b(a+1)=c a as an exact polynomial identity. -/
structure Elim where
  scale : Poly
  modBy : Poly
  target : Poly
  deriving Inhabited

def Elim.valid (c : Int) (src : Poly) (D : Elim) : Prop :=
  nf (mulP D.scale src) = nf (mulP D.modBy (surfacePoly c) ++ D.target)
instance elimValidDecidable (c : Int) (src : Poly) (D : Elim) : Decidable (D.valid c src) := by
  unfold Elim.valid
  infer_instance

theorem Elim.sound (c : Int) (src : Poly) (D : Elim) (V : D.valid c src)
    (a b : Kˣ) (P : pl a b (surfacePoly c)=0) (S : pl a b src=0) :
    pl a b D.target=0 := by
  have h := poly_eq a b _ _ V
  rw [pl_mul,S,mul_zero,pl_append,pl_mul,P,mul_zero,zero_add] at h
  exact h.symm

theorem surface_eq (c : Int) (a b : Kˣ) (H : pl a b (surfacePoly c)=0) :
    ((a:K)+1)*(b:K)=(c:K)*(a:K) := by
  have I : (a:K)*(b:K)+(b:K)-(c:K)*(a:K)=0 := by
    simpa [surfacePoly,pl,mon,sub_eq_add_neg,add_assoc] using H
  linear_combination I

theorem transport_uni (a b : Kˣ) (u : Poly) (H : ∀ z∈u, (z:RibbonAffine.Mono).2.1=0) :
    pl a b u=pl a 1 u := by
  unfold pl
  congr 1
  apply List.map_congr_left
  intro x h
  simp [mon,H x h]

structure SurfaceRow where
  trans : Elim
  mult : Elim
  deriving Inhabited

structure SurfaceGeom where
  chartIdx : Count
  coeff : Int
  rows : Array SurfaceRow
  packed : Array Nat
  deriving Inhabited

def surfacePick (G : SurfaceGeom) (i j : Nat) : Nat :=
  (G.packed[i]!/65536^j)%65536

def pairSurface (G : SurfaceGeom) (i j : Nat) : Prop :=
  let X := (chart G.chartIdx).reps[i]!
  let Y := (chart G.chartIdx).reps[j]!
  let k := surfacePick G i j
  if k=0 then X.side≠Y.side
  else let R := G.rows[k-1]!
    k-1<G.rows.size ∧ R.trans.valid G.coeff (delta X.toRow Y.toRow) ∧
      R.mult.valid G.coeff (RibbonStationaryField.factorList (X.i-Y.i) (X.j-Y.j))
instance (G : SurfaceGeom) (i j : Nat) : Decidable (pairSurface G i j) := by
  unfold pairSurface
  dsimp only
  infer_instance

def surfaceGeomValid (G : SurfaceGeom) : Prop :=
  ∀ i j : Fin (chart G.chartIdx).reps.size, i.val<j.val → pairSurface G i.val j.val
instance (G : SurfaceGeom) : Decidable (surfaceGeomValid G) := by
  unfold surfaceGeomValid
  infer_instance

theorem surface_pair_sound (G : SurfaceGeom) (H : surfaceGeomValid G)
    (a b : Kˣ) (P : pl a b (surfacePoly G.coeff)=0)
    (i j : Fin (chart G.chartIdx).reps.size) (q : i.val<j.val)
    (C : eRow a b (chart G.chartIdx).reps[i].toRow=eRow a b (chart G.chartIdx).reps[j].toRow) :
    ∃ r : Fin G.rows.size, pl a b G.rows[r].trans.target=0 ∧ pl a b G.rows[r].mult.target=0 := by
  have h := H i j q
  unfold pairSurface at h
  dsimp only at h
  rw [getElem!_pos (chart G.chartIdx).reps i.val i.isLt,
    getElem!_pos (chart G.chartIdx).reps j.val j.isLt] at h
  split at h
  · exact False.elim (h (congrArg Prod.fst C))
  · obtain ⟨k,K,L⟩ := h
    let r : Fin G.rows.size := ⟨surfacePick G i.val j.val - 1,k⟩
    have R : G.rows[surfacePick G i.val j.val - 1]! = G.rows[r] :=
      getElem!_pos G.rows _ k
    rw [R] at K L
    exact ⟨r, G.rows[r].trans.sound _ _ K a b P (delta_zero _ _ _ _ C),
      G.rows[r].mult.sound _ _ L a b P (multiplier_zero _ _ _ _ C)⟩

theorem surface_unordered (G : SurfaceGeom) (H : surfaceGeomValid G)
    (a b : Kˣ) (P : pl a b (surfacePoly G.coeff)=0)
    (N : ¬ Ordered (chart G.chartIdx) a b) :
    ∃ r : Fin G.rows.size, pl a b G.rows[r].trans.target=0 ∧ pl a b G.rows[r].mult.target=0 := by
  classical
  unfold Ordered at N
  push_neg at N
  obtain ⟨i,j,l,E⟩ := N
  exact surface_pair_sound G H a b P i j l E

end RibbonD3Field
#print axioms RibbonD3Field.surface_pair_sound
