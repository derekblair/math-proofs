import HaarSharpHeawoodCore
import HaarSharpPortGeometry

namespace HaarSharpHeawood
open HaarSharpPortGeometry
open HaarSharpLamp (words Row compatible rankLe scan scan_good compat_members)

theorem port0 : port 0 = 1 := by rfl

def row (w : List (Fin 3)) : Row :=
  ⟨key (value port true w), w.head?, w.getLast?⟩

def table (n : Nat) := List.insertionSort rankLe ((words n none).map row)

theorem cert_sound {n : Nat} (ok : scan (table n) = true) {u v : List (Fin 3)}
    (hu : u ∈ words n none) (hv : v ∈ words n none) (he : value port true u = value port true v) :
    u.head? = v.head? ∨ u.getLast? = v.getLast? := by
  have sorted : (table n).Pairwise (fun a b => a.k ≤ b.k) := by
    unfold table
    exact List.pairwise_insertionSort rankLe _
  have mem (w : List (Fin 3)) (hw : w ∈ words n none) : row w ∈ table n :=
    (List.perm_insertionSort _ _).mem_iff.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
  have c := compat_members (scan_good _ ok sorted) (mem _ hu) (mem _ hv)
  simpa [compatible,row,he] using c


set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check2 : scan (table 2) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check4 : scan (table 4) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem check8 : scan (table 8) = true := by decide +kernel
theorem no_short_cycles : ¬ HaarAllNoncommuting.HasCycle (port 1) (port 2) 4 ∧
    ¬ HaarAllNoncommuting.HasCycle (port 1) (port 2) 8 ∧
    ¬ HaarAllNoncommuting.HasCycle (port 1) (port 2) 16 :=
  ⟨no_cycle_of_check port port0 2 (by decide) (cert_sound check2),
    no_cycle_of_check port port0 4 (by decide) (cert_sound check4),
    no_cycle_of_check port port0 8 (by decide) (cert_sound check8)⟩

local notation "x" => port 1
local notation "y" => port 2

/-- Explicit port word, written from the identity in the false part. -/
def witnessWord : Array (Fin 3) := #[1,0,1,0,1,2,0,2,0,2,0,1,0,2,0,2,0,1,2,1,0,1,2,0,2,0,1,0,2,0,2,0]

def step (a : Bool × G) (p : Fin 3) : Bool × G :=
  (!a.1, a.2 * oriented port a.1 p)

theorem step_adj (a : Bool × G) (p : Fin 3) :
    HaarCycle.haarAdj x y a (step a p) := by
  obtain ⟨b,g⟩ := a
  cases b <;> fin_cases p <;> simp [HaarCycle.haarAdj,step,oriented,port0,mul_assoc]

def fromIdentity : Nat → Bool × G
  | 0 => (false,1)
  | k+1 => step (fromIdentity k) witnessWord[k]!

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem closing : fromIdentity 32 = fromIdentity 0 := by
  apply Prod.ext
  · decide +kernel
  · apply G.ext'
    · decide +kernel
    · decide +kernel

def vertex (i : Fin 32) : Bool × G := fromIdentity i.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem key_injective : Function.Injective
    (fun i : Fin 32 => ((vertex i).1,key (vertex i).2)) := by
  decide +kernel

theorem cycle32 : HaarAllNoncommuting.HasCycle x y 32 := by
  refine ⟨vertex,fun a b h => key_injective (congrArg (fun g : Bool × G => (g.1,key g.2)) h), ?_⟩
  intro i
  have e := step_adj (fromIdentity i.val) witnessWord[i.val]!
  change HaarCycle.haarAdj x y (fromIdentity i.val) (fromIdentity (i.val+1)) at e
  change HaarCycle.haarAdj x y (fromIdentity i.val) (fromIdentity ((i.val+1)%32))
  by_cases h : i.val+1 < 32
  · rw [Nat.mod_eq_of_lt h]; exact e
  · have h' : i.val+1 = 32 := by omega
    rw [h',Nat.mod_self,← closing]
    simpa only [h'] using e

theorem sharp : HaarAllNoncommuting.HasCycle x y 32 ∧
    ¬ HaarAllNoncommuting.HasCycle x y 4 ∧ ¬ HaarAllNoncommuting.HasCycle x y 8 ∧
    ¬ HaarAllNoncommuting.HasCycle x y 16 := ⟨cycle32, no_short_cycles⟩

#print axioms cardinality
#print axioms metabelian
#print axioms sharp
end HaarSharpHeawood
