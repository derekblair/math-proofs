import RibbonP3Identity
import Mathlib.Data.List.FinRange

namespace RibbonP3

/-- Class-three coefficients in y^j x^i c^k u^l v^m, and actual rim. -/
structure Row where
  rim : Bool
  i : ℤ
  j : ℤ
  k : ℤ
  l : ℤ
  m : ℤ
  deriving DecidableEq

def zeroRow : Row := ⟨false,0,0,0,0,0⟩

def march (r : Row) (p : Fin 3) : Row :=
  if p=2 then {r with rim := !r.rim}
  else if !r.rim then
    if p=0 then {r with i:=r.i+1,l:=r.l+r.k}
    else {r with i:=r.i-1,l:=r.l-r.k}
  else
    let d := r.i*(r.i-1)/2
    if p=0 then {r with j:=r.j+1,k:=r.k+r.i,l:=r.l+d,m:=r.m+r.k}
    else {r with j:=r.j-1,k:=r.k-r.i,l:=r.l-d,m:=r.m-r.k+r.i}

def rows (w : List (Fin 3)) : List Row := w.scanl march zeroRow

def table0 : Array Row := (rows a ++ ((rows b).drop 1).take 31).toArray
def table1 : Array Row := (rows ax ++ ((rows bx).drop 1).take 31).toArray
def row (t : Fin 3) (n : Fin 64) : Row :=
  (if t=2 then table1 else table0)[n.val]?.getD zeroRow

def key (q t : Fin 3) (n : Fin 64) : ℕ :=
  let r := row t n
  let c := (r.l + q.val*r.m + (r.k/3)*t.val)%3
  (if r.rim then 1 else 0) + 2*(r.i%3).toNat + 6*(r.j%3).toNat +
    18*(r.k%3).toNat + 54*c.toNat

/-- Identifies precisely the candidate collision pairs which are subsequently
separated by the common central endpoint in the actual group. -/
def rep (t : Fin 3) (i : Fin 64) : Fin 64 :=
  if i=32 then 0 else if i=63 then 1
  else if h : (t = 2 ∧ 58 ≤ i.val) ∨ (t ≠ 2 ∧ 33 ≤ i.val ∧ i.val ≤ 37) then
     ⟨64-i.val, by rcases h with h | h <;> omega⟩
  else i

def reps (t : Fin 3) : List (Fin 64) := (List.finRange 64).filter (fun i => rep t i == i)

set_option maxRecDepth 12000
set_option maxHeartbeats 0

-- Packed integer controls keep the complete kernel check small.
private def packed (q t : Fin 3) : ℕ := (![![105383997544180891545147905118012716553979467410044240951256418913933792536747754646209506614581067332531929251769054994726542399872439866288701813555712,105384166771931903968622613591583495279367066963663901050321264012723976744929138052955369599585992844615826654499916037649301451376935507286421364015616,105384336007429666726738750280390741136081640437291814108355804052734591819012510992520746297394582346186486985931043768639933241346949172662249810297344],![105383997544180891852978436623752927892402856871603734604580906899368015405057699783386830143211135382651538511368128447137813541193798780183524269097472,105384166771931904276453145097325347080916437112970918729201281377375360303103869748539266227139690091159245791167726152353486862679198817295620045537792,105384336007429667034569281786549276979786970358422654162704960479536518242579088412576743406156461535077166411760201474184598686977897280136061475095040],![105383997541417997265235074273459200893761106227692568905270374803095228494164768795234979416418478067189541281730567921795605094562162865555414597173760,105384166776885616721094766959824488149013018295171983234772943006471992764598867605922083797132983513330724124762722948503421957147717351093537423426048,105384336004666772753461006248464706931641201167263401277592457952717759622598263289772544736607598704836894543245731179611646538927244571149595213758976]] : Fin 3 → Fin 3 → ℕ) t q
private def fastKey (q t : Fin 3) (n : Fin 64) : ℕ :=
  (packed q t >>> (8*n.val)) &&& 255

private theorem fast_correct (q t : Fin 3) (n : Fin 64) : fastKey q t n = key q t n := by
  fin_cases t <;> fin_cases q <;> decide +revert

private theorem idempotent (t : Fin 3) (i : Fin 64) : rep t (rep t i) = rep t i := by decide +revert

private theorem repr_mem (t : Fin 3) (i : Fin 64) : rep t i ∈ reps t := by
  simp [reps,idempotent]

private theorem repKey (q t : Fin 3) (i : Fin 64) :
    fastKey q t (rep t i) = fastKey q t i := by
  fin_cases t <;> fin_cases q <;> decide +revert

private theorem repNodup (q t : Fin 3) : ((reps t).map (fastKey q t)).Nodup := by
  fin_cases t <;> fin_cases q <;> decide

/-- Any equality of class-three character keys lies in the prescribed
equivalence classes, for all nine slopes and carry parameters. -/
theorem collision_rep (q t : Fin 3) (i j : Fin 64) (h : key q t i = key q t j) :
    rep t i = rep t j := by
  apply List.inj_on_of_nodup_map (repNodup q t) (repr_mem t i) (repr_mem t j)
  rw [repKey,repKey,fast_correct,fast_correct]
  exact h

def abelKey (r : Row) : ℕ :=
  (if r.rim then 1 else 0) + 2*(r.i%3).toNat + 6*(r.j%3).toNat

private def abelLookup (t : Fin 3) : Array (ℤ × ℤ) :=
  if t=2 then #[(0,0),(0,0),(1,0),(1,0),(-1,0),(-1,0),(0,0),(0,1),(0,0),(1,1),(0,0),(-1,1),(0,2),(0,2),(1,2),(1,2),(-1,2),(-1,2)] else #[(0,0),(0,0),(1,0),(1,0),(2,0),(2,0),(0,0),(0,1),(0,0),(1,1),(0,0),(2,1),(0,2),(0,2),(1,2),(1,2),(2,2),(2,2)]

private theorem lifts_abelKey (t : Fin 3) (i : Fin 64) :
    ((row t i).i,(row t i).j) = (abelLookup t)[abelKey (row t i)]?.getD (0,0) := by
  fin_cases t <;> decide +revert

theorem integer_abelian_coordinates (t : Fin 3) (i j : Fin 64)
    (e : abelKey (row t i) = abelKey (row t j)) :
    (row t i).i = (row t j).i ∧ (row t i).j = (row t j).j := by
  have h := lifts_abelKey t i
  rw [e, ← lifts_abelKey] at h
  exact Prod.mk.inj h

/-- The explicit ordered list of possible same-key off-diagonal pairs. -/
theorem residual_indices (t : Fin 3) (i j : Fin 64) (lt : i < j)
    (e : rep t i = rep t j) :
    (i.val=0 ∧ j.val=32) ∨
      (i.val+j.val=64 ∧ (i.val=1 ∨
          (if t = 2 then 2 ≤ i.val ∧ i.val ≤ 6 else 27 ≤ i.val ∧ i.val ≤ 31))) := by
  fin_cases t <;> decide +kernel +revert

end RibbonP3

#print axioms RibbonP3.collision_rep
#print axioms RibbonP3.integer_abelian_coordinates
#print axioms RibbonP3.residual_indices
