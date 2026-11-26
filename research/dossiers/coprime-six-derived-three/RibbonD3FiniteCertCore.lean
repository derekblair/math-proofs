import RibbonD3FiniteUse
namespace RibbonD3Finite

structure Label where
  p : Nat
  a : Nat
  b : Nat
  deriving DecidableEq, Inhabited

def Label.triple (l : Label) : RibbonOdd.Triple := (l.p,l.a,l.b)

def Label.inp (l : Label) (da db : Nat) : Params :=
  input l.p l.a da l.b db

structure Cert where
  k : RibbonD3Field.Count
  rank : Array Nat
  order : Array Nat
  A : Array Nat
  B : Array Nat
  deriving Inhabited

def certOf (c : Cert) : RibbonD3RowSort.Sorting 127 :=
  ⟨c.rank,c.order⟩

def owner (k : RibbonD3Field.Count) (n : Fin 128) : Nat :=
  (RibbonD3Field.chart k).map[n.val]!

def good (c : Cert) (a b : Params) : Prop :=
  RibbonD3RowSort.Valid (row a c.k) (row b c.k) (owner c.k) (certOf c)
instance (c : Cert) (a b : Params) : Decidable (good c a b) := by
  unfold good
  infer_instance

def stored (c : Cert) : Prop :=
  RibbonD3RowSort.Valid c.A c.B (owner c.k) (certOf c)
instance (c : Cert) : Decidable (stored c) := by unfold stored; infer_instance

theorem from_stored {c : Cert} {a b : Params} (e : row a c.k=c.A)
    (f : row b c.k=c.B) (s : stored c) : good c a b := by
  unfold good
  rw [e,f]
  exact s

theorem same_label {k : RibbonD3Field.Count} (i j : Fin 128) (h : owner k i=owner k j) :
    RibbonD3Field.label (RibbonD3Field.raw (RibbonD3Field.chart k) i) =
    RibbonD3Field.label (RibbonD3Field.raw (RibbonD3Field.chart k) j) := by
  have S := RibbonD3Field.charts_shape k
  obtain ⟨_,e⟩ := S.2.2 i
  obtain ⟨_,f⟩ := S.2.2 j
  rw [←e,←f]
  change (RibbonD3Field.chart k).reps[owner k i]! = (RibbonD3Field.chart k).reps[owner k j]!
  rw [h]

theorem cert_sound {c : Cert} {a b : Params} (v : good c a b) (i j : Fin 128)
    (ea : (row a c.k)[i.val]! = (row a c.k)[j.val]!)
    (eb : (row b c.k)[i.val]! = (row b c.k)[j.val]!) :
    RibbonD3Field.label (RibbonD3Field.raw (RibbonD3Field.chart c.k) i) =
    RibbonD3Field.label (RibbonD3Field.raw (RibbonD3Field.chart c.k) j) :=
  same_label i j (RibbonD3RowSort.checked v i j ea eb)

end RibbonD3Finite
