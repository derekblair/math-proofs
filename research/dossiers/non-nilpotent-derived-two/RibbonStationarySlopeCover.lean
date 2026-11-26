import RibbonStationarySlopes
import RibbonStationarySymbols

namespace RibbonStationaryField
open RibbonStationaryWord
open RibbonAffine (pl eRow)
variable {K : Type*} [Field K]

structure CheckRow where
  e : Nat
  tr : Poly
  cert : SlopeID
  deriving Inhabited

structure Cover where
  k : Count
  rows : Array CheckRow
  positions : Array Nat
  deriving Inhabited

inductive Route where
  | side
  | mate
  | one (u2 v3 : Nat)
  | use (k u2 v3 : Nat) (shift : Int)
  deriving Inhabited

def decode (n : Nat) : Route :=
  if n=0 then .side else if n=1 then .mate else if n<66 then
    .one ((n-2)%8) ((n-2)/8) else
    let w := n-66
    .use (w%64) ((w/64)%8) ((w/512)%8) ((w/4096:Int)-32)

def route (C : Cover) (i j : Fin 64) : Route :=
  decode (((C.positions[i.val]!) / 262144^j.val)%262144)

def RowValid (B : Poly) (C : Cover) : Prop :=
  ∀ r : Fin C.rows.size,
    let z := C.rows[r]
    slopeValid B ⟨0,0,z.e,0,z.tr⟩ z.cert
instance (B : Poly) (C : Cover) : Decidable (RowValid B C) := by unfold RowValid; infer_instance

def RouteValid (B : Branch) (C : Cover) (i j : Fin 64) : Route → Prop :=
  let P := sym C.k i
  let Q := sym C.k j
  fun
  | .side => P.side≠Q.side
  | .mate => IsMate (spec C.k) i.val j.val
  | .one u v => (B.v*(P.i-Q.i)-B.u*(P.j-Q.j)).natAbs=1*(2^u*3^v)
  | .use k u v shift => k<C.rows.size ∧
      transitionValid B.u B.v P Q ⟨u,v,C.rows[k]!.e,shift,C.rows[k]!.tr⟩

instance routeDecidable (B : Branch) (C : Cover) (i j : Fin 64) (r : Route) :
    Decidable (RouteValid B C i j r) := by cases r <;> unfold RouteValid <;> dsimp only <;> infer_instance

def GeomValid (B : Branch) (C : Cover) : Prop :=
  ∀ i j : Fin 64, i.val<j.val → RouteValid B C i j (route C i j)
instance (B : Branch) (C : Cover) : Decidable (GeomValid B C) := by unfold GeomValid; infer_instance

theorem no_fallback_collision (B : Branch) (C : Cover) (V : RowValid B.p C) (g : GeomValid B C)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (nt : t≠1)
    (F : pl t 1 B.p=0) (i j : Fin 64) (lt : i.val<j.val)
    (eq : eRow (t^B.v) (t^(-B.u)) (symbol C.k i.val)=eRow (t^B.v) (t^(-B.u)) (symbol C.k j.val)) :
    IsMate (spec C.k) i.val j.val ∨
    ∃ k : Fin C.rows.size, pl t 1 C.rows[k].tr=0 ∧ pl t 1 (binom C.rows[k].e)=0 ∧ (C.rows[k].cert.n:K)=0 := by
  let X := symbol C.k i.val
  let Y := symbol C.k j.val
  have q := g i j lt
  cases h : route C i j with
  | side =>
    rw [h] at q
    exact False.elim (q (by simpa only [sym_ok,eRow] using congrArg Prod.fst eq))
  | mate =>
    rw [h] at q
    exact Or.inl q
  | one u v =>
    rw [h] at q
    have hp := (collision_param B.u B.v t _ _ rfl rfl X Y eq).1
    have r := coprime_drop n odd no3 t tn _ 1 u v (by simpa only [RouteValid,sym_ok] using q) hp
    exact False.elim (nt (by simpa using r))
  | use k u v s =>
    rw [h] at q
    obtain ⟨kV,E⟩ := q
    let r : Fin C.rows.size := ⟨k,kV⟩
    let w : Transition := ⟨u,v,C.rows[r].e,s,C.rows[r].tr⟩
    have hW : transitionValid B.u B.v X Y w := by
      simpa only [w,r,X,Y,sym_ok,Fin.getElem_fin,getElem!_pos C.rows k kV] using E
    obtain ⟨b,z⟩ := transition_sound B.u B.v t _ _ n odd no3 tn rfl rfl X Y w hW eq
    exact Or.inr ⟨r,z,b,slope_sound t B.p w C.rows[r].cert (V r) F z b⟩

end RibbonStationaryField
#print axioms RibbonStationaryField.no_fallback_collision
