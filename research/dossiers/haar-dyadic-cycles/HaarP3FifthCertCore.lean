import HaarP3CollectSteps
import HaarClass5DirTables
import HaarMatrixPackedCheck

namespace HaarP3FifthCert
open HaarP3CollectCore HaarP3CollectActions HaarP3CollectSteps
open HaarCycle HaarAllNoncommuting

structure Cert where
  t : Fin 4
  rows : Array Grid
  low : Array (ℤ × ℤ)
  mid : Array ℤ
  deriving Inhabited

def row (C : Cert) (i : ℕ) := C.rows[i]!
def digit (a : ℤ) : ℕ := (a%3).toNat
def lowKey (r : Grid) : ℕ := digit r.i * 3 + digit r.j
def midKey (r : Grid) : ℕ := lowKey r * 3 + digit r.n.k
def tailKey (r : Grid) : ℕ := ((midKey r * 3 + digit r.n.u)*3 + digit r.n.a)*3 + digit r.n.z
def key (r : Grid) (i : ℕ) : ℕ := (i%2)*729 + tailKey r

def label (C : Cert) (i : ℕ) : Fin 3 := HaarReducedWalkCycle.label (HaarClass5DirTables.W C.t) i

def zeroGrid : Grid := ⟨0,0,zero⟩

def StepAt (p : Params) (C : Cert) (i : Fin 64) : Prop :=
  let a := row C i.val
  let b := row C (i.val+1)
  let h := label C i.val
  if i.val%2=0 then (a=negStep p h b ∧ (h=2 → rangeI b))
  else (b=negStep p h a ∧ (h=2 → rangeI a))
instance (p : Params) (C : Cert) (i : Fin 64) : Decidable (StepAt p C i) := by
  unfold StepAt; dsimp only; split <;> infer_instance

def CanonAt (C : Cert) (i : Fin 64) : Prop :=
  let r := row C i.val
  C.low[(i.val%2)*9+lowKey r]! = (r.i,r.j) ∧ C.mid[(i.val%2)*27+midKey r]! = r.n.k ∧
  (0≤r.n.u ∧ r.n.u<3) ∧ (0≤r.n.a ∧ r.n.a<3) ∧ (0≤r.n.z ∧ r.n.z<3)
instance (C : Cert) (i : Fin 64) : Decidable (CanonAt C i) := by
  unfold CanonAt; infer_instance

def keys (C : Cert) : List ℕ := List.ofFn (fun i : Fin 64 => key (row C i.val) i.val)

def Valid (p : Params) (C : Cert) : Prop :=
  row C 0=zeroGrid ∧ row C 64=zeroGrid ∧ corrTest p ∧ (∀ i, StepAt p C i) ∧
    (∀ i, CanonAt C i) ∧ (keys C).Nodup

instance (p : Params) (C : Cert) : Decidable (Valid p C) := by unfold Valid; infer_instance

theorem key_inj (C : Cert) (p : Params) (ok : Valid p C) :
    Function.Injective (fun i : Fin 64 => key (row C i.val) i.val) := by
  have nd' := ok.2.2.2.2.2
  intro i j e
  have inj := nd'.injective_get
  have H : (keys C).get ⟨i.val,by simpa only [keys,List.length_ofFn] using i.isLt⟩ =
      (keys C).get ⟨j.val,by simpa only [keys,List.length_ofFn] using j.isLt⟩ := by
    simpa only [keys,List.get_eq_getElem,List.getElem_ofFn] using e
  exact Fin.ext (congrArg Fin.val (inj H))

theorem digit_congr {a b : ℤ} (eq : (a-b)%3=0) : digit a=digit b := by
  unfold digit
  congr 1
  omega

theorem digit_small {a : ℤ} (h : 0≤a ∧ a<3) : (digit a : ℤ)=a := by
  unfold digit
  rw [Int.emod_eq_of_lt h.1 h.2,Int.toNat_of_nonneg h.1]

theorem valid_pair (C : Cert) (p : Params) (ok : Valid p C) (i j : Fin 64)
    (side : i.val%2=j.val%2)
    (I : ((row C i.val).i-(row C j.val).i)%3=0)
    (J : ((row C i.val).j-(row C j.val).j)%3=0)
    (K : (row C i.val).i=(row C j.val).i → (row C i.val).j=(row C j.val).j →
      ((row C i.val).n.k-(row C j.val).n.k)%3=0)
    (T : (row C i.val).i=(row C j.val).i → (row C i.val).j=(row C j.val).j →
      (row C i.val).n.k=(row C j.val).n.k →
      (row C i.val).n.u=(row C j.val).n.u ∧ (row C i.val).n.a=(row C j.val).n.a ∧
        (row C i.val).n.z=(row C j.val).n.z) : i=j := by
  have ci := ok.2.2.2.2.1 i
  have cj := ok.2.2.2.2.1 j
  have lo : lowKey (row C i.val)=lowKey (row C j.val) := by
    simp only [lowKey,digit_congr I,digit_congr J]
  have xy : ((row C i.val).i,(row C i.val).j) = ((row C j.val).i,(row C j.val).j) := by
    rw [←ci.1,←cj.1,lo,side]
  have eI := congrArg Prod.fst xy
  have eJ := congrArg Prod.snd xy
  have mi : midKey (row C i.val)=midKey (row C j.val) := by
    simp only [midKey,lo,digit_congr (K eI eJ)]
  have ez : (row C i.val).n.k=(row C j.val).n.k := by
    rw [←ci.2.1,←cj.2.1,mi,side]
  obtain ⟨u,a,b⟩ := T eI eJ ez
  apply key_inj C p ok
  simp only [key,tailKey,mi,u,a,b,side]

end HaarP3FifthCert
#print axioms HaarP3FifthCert.valid_pair
