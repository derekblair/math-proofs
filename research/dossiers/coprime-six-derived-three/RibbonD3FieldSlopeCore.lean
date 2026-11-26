import RibbonD3FieldCharts
import RibbonStationarySlopes

namespace RibbonD3Field
open RibbonStationaryField (Branch Poly Transition transitionValid transition_sound
  collision_param coprime_drop binom Id natConst)
open RibbonAffine (pl eRow mon)
variable {K : Type*} [Field K]

structure SlopeRow where
  exponent : Nat
  trans : Poly
  deriving Inhabited

structure SlopeGeom where
  word : Count
  rows : Array SlopeRow
  packed : Array Nat
  deriving Inhabited

inductive Route where
  | side
  | one (twoP threeP : Nat)
  | some (i twoP threeP : Nat) (shift : Int)
  deriving Inhabited

def decode (n : Nat) : Route :=
  if n=0 then .side else if n<65 then .one ((n-1)%8) ((n-1)/8) else
    let z := n-65
    .some (z%512) ((z/512)%8) ((z/4096)%8) ((z/32768:Int)-32)

def select (G : SlopeGeom) (i j : Nat) : Route :=
  decode (((G.packed[i]!)/4194304^j)%4194304)

def RouteValid (G : SlopeGeom) (u v : Int) (i j : Nat) : Route→Prop :=
  let P := (chart G.word).reps[i]!
  let Q := (chart G.word).reps[j]!
  fun
  | .side => P.side≠Q.side
  | .one e f => (v*(P.i-Q.i)-u*(P.j-Q.j)).natAbs=1*(2^e*3^f)
  | .some k e f shift => k<G.rows.size ∧
      transitionValid u v P.toRow Q.toRow ⟨e,f,G.rows[k]!.exponent,shift,G.rows[k]!.trans⟩
instance (G : SlopeGeom) (u v : Int) (i j : Nat) (R : Route) : Decidable (RouteValid G u v i j R) := by
  cases R <;> unfold RouteValid <;> dsimp only <;> infer_instance

def GeomValid (G : SlopeGeom) (u v : Int) : Prop :=
  ∀ i j : Fin (chart G.word).reps.size, i.val<j.val → RouteValid G u v i.val j.val (select G i.val j.val)
instance (G : SlopeGeom) (u v : Int) : Decidable (GeomValid G u v) := by unfold GeomValid; infer_instance

def geomRowCheck (G : SlopeGeom) (u v : Int) (i : Nat) : Bool :=
  (List.range (chart G.word).reps.size).all fun j =>
    if i<j then decide (RouteValid G u v i j (select G i j)) else true

def geomChunkCheck (G : SlopeGeom) (u v : Int) (c : Fin 16) : Bool :=
  (List.range 8).all fun i =>
    if 8*c.val+i<(chart G.word).reps.size then geomRowCheck G u v (8*c.val+i) else true

theorem geom_by_chunks (G : SlopeGeom) (u v : Int) (N : (chart G.word).reps.size≤128)
    (hc : ∀ c : Fin 16, geomChunkCheck G u v c=true) : GeomValid G u v := by
  intro i j l
  have hi := i.isLt
  have h : i.val/8<16 := by omega
  let c : Fin 16 := ⟨i.val/8,h⟩
  have e : 8*c.val+i.val%8=i.val := by dsimp [c]; omega
  have R := List.all_eq_true.mp (hc c) (i.val%8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have I : geomRowCheck G u v i.val=true := by simpa only [e,hi,ite_true] using R
  have J := List.all_eq_true.mp I j.val (List.mem_range.mpr j.isLt)
  exact of_decide_eq_true (by simpa only [l,ite_true] using J)

theorem geometry_sound (G : SlopeGeom) (u v : Int) (H : GeomValid G u v)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1)
    (i j : Fin (chart G.word).reps.size) (l : i.val<j.val)
    (E : eRow (t^v) (t^(-u)) (chart G.word).reps[i].toRow =
      eRow (t^v) (t^(-u)) (chart G.word).reps[j].toRow) :
    ∃ k : Fin G.rows.size, pl t 1 G.rows[k].trans=0 ∧ pl t 1 (binom G.rows[k].exponent)=0 := by
  have q := H i j l
  let P := (chart G.word).reps[i].toRow
  let Q := (chart G.word).reps[j].toRow
  have L : eRow (t^v) (t^(-u)) P=eRow (t^v) (t^(-u)) Q := E
  have iH : i.val < (chart G.word).reps.size := i.isLt
  have jH : j.val < (chart G.word).reps.size := j.isLt
  have H1 := getElem!_pos (chart G.word).reps i.val iH
  have H2 := getElem!_pos (chart G.word).reps j.val jH
  cases h : select G i.val j.val with
  | side =>
    rw [h] at q
    change ((chart G.word).reps[i.val]!).side ≠ ((chart G.word).reps[j.val]!).side at q
    rw [H1,H2] at q
    exact False.elim (q (congrArg Prod.fst L))
  | one e f =>
    rw [h] at q
    have nc := (collision_param u v t _ _ rfl rfl P Q L).1
    have H : (v*(P.i-Q.i)-u*(P.j-Q.j)).natAbs=1*(2^e*3^f) := by
      simpa only [RouteValid,H1,H2,P,Q,Label.toRow,Fin.getElem_fin] using q
    have R := coprime_drop n odd no3 t tn _ 1 e f H nc
    exact False.elim (t1 (by simpa using R))
  | some k e f s =>
    rw [h] at q
    obtain ⟨K,T⟩ := q
    let k' : Fin G.rows.size := ⟨k,K⟩
    let w : Transition := ⟨e,f,G.rows[k'].exponent,s,G.rows[k'].trans⟩
    have V : transitionValid u v P Q w := by
      simpa only [H1,H2,P,Q,w,k',Fin.getElem_fin,getElem!_pos G.rows k K] using T
    have ⟨B,T⟩ := transition_sound u v t _ _ n odd no3 tn rfl rfl P Q w V L
    exact ⟨k',T,B⟩

structure ModBlock where
  certs : Array Id
  deriving Inhabited

def blockValid (p : Nat) (f : Poly) (G : SlopeGeom) (B : ModBlock) : Prop :=
  ∀ i : Fin G.rows.size,
    B.certs[i.val]!.rhs = natConst 1 ∧
    B.certs[i.val]!.valid f G.rows[i].trans (binom G.rows[i].exponent) p
instance (p : Nat) (f : Poly) (G : SlopeGeom) (B : ModBlock) :
    Decidable (blockValid p f G B) := by unfold blockValid; infer_instance

theorem block_sound (G : SlopeGeom) (u v : Int) (GV : GeomValid G u v)
    (p : Nat) (f : Poly) (B : ModBlock) (BV : blockValid p f G B)
    (t : Kˣ) (n : Nat) (odd : Odd n) (no3 : ¬3∣n) (tn : t^n=1) (t1 : t≠1)
    (P : (p:K)=0) (F : pl t 1 f=0) :
    Ordered (chart G.word) (t^v) (t^(-u)) := by
  intro i j l eq
  obtain ⟨s,T,E⟩ := geometry_sound G u v GV t n odd no3 tn t1 i j l eq
  have ⟨H,I⟩ := BV s
  have z := (B.certs[s.val]!).sound f _ _ p I t F T E (by simpa using P)
  rw [H] at z
  exact (one_ne_zero : (1:K)≠0) (by simpa [natConst,pl,mon] using z)

end RibbonD3Field
#print axioms RibbonD3Field.geometry_sound
#print axioms RibbonD3Field.block_sound
