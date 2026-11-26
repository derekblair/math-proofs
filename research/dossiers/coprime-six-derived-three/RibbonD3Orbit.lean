import RibbonD3OrbitData
import RibbonD3FiniteTransport

namespace RibbonD3Finite
set_option maxRecDepth 25000
set_option maxHeartbeats 0
open RibbonD3Stationary
abbrev B := Fin 52
abbrev PP := Fin 213
abbrev JJ := Fin 137

def getBad (i : B) : Label := bads[i.val]!
def Bad (t : RibbonOdd.Triple) : Prop :=
  ∃ i : B, (getBad i).triple = t

def pairLabel (i : PP) : Label × Label := pairLabels[i.val]!
def jetLabel (i : JJ) : Label × Nat × Nat := jetLabels[i.val]!

def baseMotion (l : Label) (n : Nat) : Label := (acted l 0 0 n 1).1

def PairResult (i j : B) : Prop :=
  let (m,c,flip) := (pairMotions[i.val]!)[j.val]!
  let t := pairLabels[c]!
  c < 213 ∧
    (if flip=1 then (t.2,t.1) else t) =
      (baseMotion (getBad i) m,baseMotion (getBad j) m)

abbrev Direction (i : B) := Fin ((getBad i).p+1)
def rawDir {i : B} (d : Direction i) : Nat × Nat :=
  if d.val=0 then (0,1) else (1,d.val-1)
def JetResult (i : B) (d : Direction i) : Prop :=
  let (m,c,s) := (jetMotions[i.val]!)[d.val]!
  c<137 ∧ jetLabels[c]! = acted (getBad i) (rawDir d).1 (rawDir d).2 m s

instance (i j : B) : Decidable (PairResult i j) := by
  unfold PairResult
  infer_instance
instance (i : B) (d : Direction i) : Decidable (JetResult i d) := by
  unfold JetResult
  infer_instance

theorem choosePair (i j : B) (H : PairResult i j) :
    ∃ (m : Nat) (c : PP),
      (baseMotion (getBad i) m,baseMotion (getBad j) m)=pairLabel c ∨
      (baseMotion (getBad j) m,baseMotion (getBad i) m)=pairLabel c := by
  let r := (pairMotions[i.val]!)[j.val]!
  have H' := H.2
  have h : r.2.1 < 213 := H.1
  refine ⟨r.1,⟨r.2.1,h⟩,?_⟩
  change (if r.2.2=1 then ((pairLabels[r.2.1]!).2,(pairLabels[r.2.1]!).1)
    else pairLabels[r.2.1]!) = _ at H'
  by_cases e : r.2.2=1
  · right
    rw [if_pos e] at H'
    exact Prod.ext (Prod.mk.inj H').2.symm (Prod.mk.inj H').1.symm
  · left
    rw [if_neg e] at H'
    exact H'.symm

theorem chooseJet (i : B) (d : Direction i) (H : JetResult i d) :
    ∃ (m s : Nat) (c : JJ),
      acted (getBad i) (rawDir d).1 (rawDir d).2 m s=jetLabel c := by
  let r := (jetMotions[i.val]!)[d.val]!
  exact ⟨r.1,r.2.2,⟨r.2.1,H.1⟩,H.2.symm⟩

theorem chooseDirection {i : B} {p : Nat} [Fact p.Prime] (ep : p=(getBad i).p)
    (da db : ZMod p) (h : da≠0 ∨ db≠0) :
    ∃ s : ZMod p, ∃ d : Direction i, ((s*da).val,(s*db).val)=rawDir d := by
  subst p
  have p1 : (getBad i).p≠1 := (Fact.out : (getBad i).p.Prime).ne_one
  by_cases a : da=0
  · have b := h.resolve_left (fun z => z a)
    exact ⟨db⁻¹,0,by simp [a,b,rawDir,ZMod.val_one'' p1]⟩
  · let s := da⁻¹*db
    have sv := ZMod.val_lt s
    refine ⟨da⁻¹,⟨s.val+1,by omega⟩,?_⟩
    have d0 : s.val+1≠0 := by omega
    exact Prod.ext (by simp [a,rawDir,d0,ZMod.val_one'' p1]) (by simp [s,rawDir,d0])

end RibbonD3Finite
