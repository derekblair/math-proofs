import RibbonD3Mixed3Data
namespace RibbonD3Mixed3
open Ribbon5Bridge RibbonD3WordSelection RibbonD3Low RibbonD3PortEval RibbonAffine

def k3 (k : Fin 3) : Count := ⟨k.val, by omega⟩
def C (k : Fin 3) := RibbonD3Field.chart (k3 k)
def reps (k : Fin 3) := (C k).reps
def mp (k : Fin 3) := (C k).map
def tags (k : Fin 3) := tagFun 3 (bank k)
def inside (k : Fin 3) (q : Q) : Prop :=
  let x := if k.val = 2 then -2 else 0
  let y := if k.val = 1 then 0 else -2
  x ≤ q.2.1 ∧ q.2.1 ≤ x+2 ∧ y ≤ q.2.2.1 ∧ q.2.2.1 ≤ y+2
instance (k : Fin 3) (q : Q) : Decidable (inside k q) := by unfold inside; infer_instance
private theorem steps (k : Fin 3) : ∀ n : Fin 128,
    push (tab k)[n.val]! (block (k3 k) 128)[n.val]! = (tab k)[n.val+1]! := by
  fin_cases k <;> decide +kernel
private theorem initial (k : Fin 3) : (tab k)[0]! = (false,0,0,0) := by
  fin_cases k <;> decide +kernel

theorem low_tab (k : Fin 3) (n : Nat) (hn : n ≤ 128) :
    low (k3 k) n = (tab k)[n]! := by
  induction n with
  | zero => exact (initial k).symm
  | succ n ih =>
    have n0 : n < 128 := by omega
    have E : n < (block (k3 k) 128).length := by
      rwa [RibbonD3ChartCycles.length_block _ _ (le_refl 128)]
    have pref (i : Nat) (hi : i ≤ 128) :
        block (k3 k) i = (block (k3 k) 128).take i := by
      simp [block,decode,List.map_take,List.take_take,Nat.min_eq_left hi]
    have H : low (k3 k) (n+1) =
        push (low (k3 k) n) (block (k3 k) 128)[n]! := by
      unfold low
      rw [pref (n+1) hn,pref n (by omega),List.take_succ_eq_append_getElem E]
      rw [List.foldl_append,getElem!_pos (block (k3 k) 128) n E]
      rfl
    rw [H,ih (by omega)]
    exact steps k ⟨n,n0⟩

set_option maxHeartbeats 3000000 in
private theorem slice (k : Fin 3) (g : Fin 8) : ∀ i : Fin 16,
    let n := g.val*16+i.val
    inside k (tab k)[n]! ∧ (mp k)[n]! ∈ tags k (tab k)[n]! := by
  fin_cases k <;> fin_cases g <;> decide +kernel

theorem position (k : Fin 3) (i : Fin 128) :
    inside k (low (k3 k) i.val) ∧ (mp k)[i.val]! ∈ tags k (low (k3 k) i.val) := by
  obtain ⟨g,h,e⟩ := split128 i
  have Q := slice k g h
  change inside k (tab k)[g.val*16+h.val]! ∧ (mp k)[g.val*16+h.val]! ∈
    tags k (tab k)[g.val*16+h.val]! at Q
  rw [e] at Q
  rw [low_tab k i.val i.isLt.le]
  exact Q

def fmono (k f : Fin 3) : List Mono :=
  if f.val = 0 then [(0,0,1)] else
  if k.val = 0 then
    if f.val = 1 then [(1,1,1),(1,0,1),(0,1,1)] else [(1,1,1),(1,0,-2),(0,1,1)]
  else if k.val = 1 then
    if f.val = 1 then [(1,1,2),(1,0,-1),(0,0,-1)] else [(1,1,1),(1,0,1),(0,0,1)]
  else
    if f.val = 1 then [(1,1,1),(0,1,1),(0,0,-2)] else [(1,1,1),(0,1,1),(0,0,1)]

abbrev Fact := Nat × Nat × ℤ × ℤ × ℤ × Fin 3

def covers (k : Fin 3) (i j : Nat) : Bool :=
  (factors k).any fun f => f.1 == i && f.2.1 == j

def tagsCovered (k : Fin 3) : Bool :=
  (bank k).all fun d => d.2.all fun i => d.2.all fun j => !(i<j) || covers k i j

theorem tagsCovered_true (k : Fin 3) : tagsCovered k = true := by
  fin_cases k <;> decide +kernel

def check (k : Fin 3) (f : Fact) : Bool :=
  let ⟨i,j,u,v,c,t⟩ := f
  decide (c = 1 ∨ c = -1 ∨ c = 3 ∨ c = -3) &&
  decide (nf ((reps k)[i]!.tr ++ negative (reps k)[j]!.tr) =
       nf (mulP (mulP [(u,v,c)] [(1,0,1),(0,0,-1)]) (fmono k t)))

theorem checks (k : Fin 3) : (factors k).all (check k) = true := by
  fin_cases k <;> decide +kernel

theorem withinTag (k : Fin 3) (q : Q) (i j : Nat)
    (hi : i ∈ tags k q) (hj : j ∈ tags k q) (lt : i < j) : covers k i j = true := by
  unfold tags tagFun at hi hj
  cases E : (bank k).find? (fun r => r.1 == lowKey 3 q) with
  | none => simp [E] at hi
  | some m =>
    have M := List.mem_of_find?_eq_some E
    have T := List.all_eq_true.mp (tagsCovered_true k) m M
    have iM : i ∈ m.2 := by simpa [E] using hi
    have jM : j ∈ m.2 := by simpa [E] using hj
    have Q := List.all_eq_true.mp (List.all_eq_true.mp T i iM) j jM
    simpa [lt] using Q
end RibbonD3Mixed3
