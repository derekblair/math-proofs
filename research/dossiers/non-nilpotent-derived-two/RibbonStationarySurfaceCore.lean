import RibbonStationaryModular
import RibbonStationarySymbols

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (Row Mono pl mon nf mulP poly_eq pl_mul pl_append eRow delta delta_zero rel_from_mul)
variable {K : Type*} [Field K]

def factorList (a b : Int) : Poly := [(a,b,1),(0,0,-1)]
def surfaceBinom (e : Nat) : Poly := [(0,e,1),(0,0,-1)]

theorem multiplier_zero (a b : Kˣ) (P Q : Row) (hit : eRow a b P=eRow a b Q) :
    pl a b (factorList (P.i-Q.i) (P.j-Q.j))=0 := by
  have e : a^P.i*b^P.j=a^Q.i*b^Q.j := congrArg (fun z : Bool×Kˣ×K => z.2.1) hit
  have q := rel_from_mul a b P.i P.j Q.i Q.j e
  simp [factorList,pl,mon,q]

/-- Elimination of the first Laurent variable under 2a+1=0. The
certificate includes all factors introduced for clearing denominators. -/
structure Specialization where
  scale : Mono
  quot : Poly
  out : Poly
  deriving Inhabited

def Specialization.valid (w : Specialization) (P : Poly) : Prop :=
  nf (mulP [w.scale] P)=nf (mulP w.quot sideA0++w.out)
instance specializationDecidable (w : Specialization) (P : Poly) : Decidable (w.valid P) := by
  unfold Specialization.valid; infer_instance

theorem Specialization.sound (w : Specialization) (P : Poly) (v : w.valid P)
    (a b : Kˣ) (surface : pl a b sideA0=0) (root : pl a b P=0) :
    pl a b w.out=0 := by
  have h := poly_eq a b _ _ v
  rw [pl_mul,root,mul_zero,pl_append,pl_mul,surface,mul_zero,zero_add] at h
  exact h.symm

/-- A universally checkable identity over two Laurent variables. -/
theorem id_sound_surface (I : Id) (f g h : Poly) (p : Int) (C : I.valid f g h p) (a b : Kˣ)
    (F : pl a b f=0) (G : pl a b g=0) (H : pl a b h=0) (P : (p:K)=0) :
    pl a b I.rhs=0 := by
  have T := poly_eq a b _ _ C
  rw [add3,pl_append,pl_append,pl_append,pl_mul,pl_mul,pl_mul,zscale,pl_mul,F,G,H] at T
  have R : pl a b (natConst p)=0 := by simp [natConst,pl,mon,P]
  rw [R,zero_mul,mul_zero,mul_zero,mul_zero,add_zero,add_zero,add_zero] at T
  exact T.symm

structure SurfaceRow where
  trans : Specialization
  multiplier : Specialization
  constant : Int
  ordinary : Id
  mod11 : Id
  mod43 : Id
  deriving Inhabited

structure SurfaceSpec where
  word : Count
  rows : Array SurfaceRow
  route : Array Nat
  normal : Poly
  mod11 : Poly
  mod43 : Poly
  deriving Inhabited

def SurfacePair (S : SurfaceSpec) (i j : Fin 64) (r : Fin S.rows.size) : Prop :=
  S.rows[r].trans.valid (delta (sym S.word i) (sym S.word j)) ∧
  S.rows[r].multiplier.valid (factorList ((sym S.word i).i-(sym S.word j).i)
    ((sym S.word i).j-(sym S.word j).j))

def surfaceDecode (S : SurfaceSpec) (i j : Fin 64) : Nat :=
  ((S.route[i.val]!)/(1024^j.val))%1024

def SurfaceShape (S : SurfaceSpec) (i j : Fin 64) : Prop :=
  let k := surfaceDecode S i j
  if k=0 then (sym S.word i).side≠(sym S.word j).side
  else if k=1 then IsMate (spec S.word) i.val j.val
  else if h : k-2<S.rows.size then SurfacePair S i j ⟨k-2,h⟩ else False

instance surfPairDecidable (S : SurfaceSpec) (i j : Fin 64) (r : Fin S.rows.size) :
    Decidable (SurfacePair S i j r) := by unfold SurfacePair; infer_instance
instance surfShapeDecidable (S : SurfaceSpec) (i j : Fin 64) : Decidable (SurfaceShape S i j) := by
  unfold SurfaceShape; dsimp only
  split
  · infer_instance
  · split
    · infer_instance
    · split <;> infer_instance

def SurfaceGeom (S : SurfaceSpec) : Prop :=
  ∀ i j : Fin 64, i.val<j.val → SurfaceShape S i j
instance surfGeomDecidable (S : SurfaceSpec) : Decidable (SurfaceGeom S) := by unfold SurfaceGeom; infer_instance

def surfaceOrdinary (case : SurfaceSpec) (r : Fin case.rows.size) (N : Int) : Prop :=
  let x := case.rows[r]
  x.constant ∣ N ∧
  x.ordinary.rhs=mulP (natConst x.constant) case.normal ∧
  x.ordinary.valid x.trans.out x.multiplier.out [] 0

def surfaceMod (case : SurfaceSpec) (r : Fin case.rows.size) (j : Bool) : Prop :=
  let x := case.rows[r]
  let (p,C,out) := if j then (11,x.mod11,case.mod11) else (43,x.mod43,case.mod43)
  C.rhs=out ∧ C.valid x.trans.out x.multiplier.out [] p
instance ordinaryDecidable (S : SurfaceSpec) (r : Fin S.rows.size) (N : Int) :
    Decidable (surfaceOrdinary S r N) := by unfold surfaceOrdinary; infer_instance
instance surfModDecidable (S : SurfaceSpec) (r : Fin S.rows.size) (j : Bool) :
    Decidable (surfaceMod S r j) := by cases j <;> unfold surfaceMod <;> dsimp only <;> infer_instance

theorem surface_collision (S : SurfaceSpec) (r : Fin S.rows.size) (a b : Kˣ)
    (i j : Fin 64) (P : SurfacePair S i j r) (sur : pl a b sideA0=0)
    (eq : eRow a b (symbol S.word i.val)=eRow a b (symbol S.word j.val)) :
    pl a b S.rows[r].trans.out=0 ∧ pl a b S.rows[r].multiplier.out=0 := by
  exact ⟨S.rows[r].trans.sound _ P.1 a b sur (by simpa only [sym_ok] using delta_zero a b _ _ eq),
    S.rows[r].multiplier.sound _ P.2 a b sur (by simpa only [sym_ok] using multiplier_zero a b _ _ eq)⟩

theorem cases_surface (S : SurfaceSpec) (a b : Kˣ) (G : SurfaceGeom S) (i j : Fin 64)
    (lt : i.val<j.val) (sur : pl a b sideA0=0)
    (eq : eRow a b (symbol S.word i.val)=eRow a b (symbol S.word j.val)) :
    IsMate (spec S.word) i.val j.val ∨
      ∃ r : Fin S.rows.size, pl a b S.rows[r].trans.out=0 ∧ pl a b S.rows[r].multiplier.out=0 := by
  have h := G i j lt
  unfold SurfaceShape at h
  dsimp only at h
  split at h
  · exact False.elim (h (by simpa only [sym_ok,eRow] using congrArg Prod.fst eq))
  split at h
  · exact Or.inl h
  · split at h
    · exact Or.inr ⟨_,surface_collision S _ a b i j h sur eq⟩
    · exact False.elim h

theorem collect_ordinary (S : SurfaceSpec) (a b : Kˣ) (N : Int)
    (V : ∀ r, surfaceOrdinary S r N) (nz : (N:K)≠0)
    (r : Fin S.rows.size) (A : pl a b S.rows[r].trans.out=0) (B : pl a b S.rows[r].multiplier.out=0) :
    pl a b S.normal=0 := by
  have ⟨d,out,valid⟩ := V r
  have q := id_sound_surface _ _ _ _ 0 valid a b A B rfl (by simp)
  rw [out,pl_mul] at q
  have E : (S.rows[r].constant:K)≠0 := by
    obtain ⟨c,h⟩ := d
    intro Z
    apply nz
    rw [h,Int.cast_mul,Z,zero_mul]
  apply (mul_eq_zero.mp q).resolve_left
  simpa [natConst,pl,mon] using E

theorem collect_modular (S : SurfaceSpec) (a b : Kˣ) (j : Bool)
    (V : ∀ r, surfaceMod S r j) (p : ((if j then (11:ℤ) else 43):K)=0)
    (r : Fin S.rows.size) (A : pl a b S.rows[r].trans.out=0) (B : pl a b S.rows[r].multiplier.out=0) :
    pl a b (if j then S.mod11 else S.mod43)=0 := by
  cases j
  · have ⟨out,valid⟩ := V r
    rw [←out]
    exact id_sound_surface _ _ _ _ 43 valid a b A B rfl (by simpa using p)
  · have ⟨out,valid⟩ := V r
    rw [←out]
    exact id_sound_surface _ _ _ _ 11 valid a b A B rfl (by simpa using p)

end RibbonStationaryField
#print axioms RibbonStationaryField.cases_surface
#print axioms RibbonStationaryField.collect_modular
