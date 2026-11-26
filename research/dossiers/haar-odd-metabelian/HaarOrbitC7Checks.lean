import HaarOrbitC7Data
import HaarOrbitChains
namespace HaarOrbitC7Checks
open HaarOrbitC7DAG HaarOrbitC7Data HaarOrbitC7Voltage HaarOrbitChains HaarOrbitVoltage
set_option maxRecDepth 40000
set_option maxHeartbeats 0
abbrev E := Fin 21
abbrev S := Fin 7
def src : E → B := ![0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6]
def dst : E → B := ![7,8,10,8,9,11,9,10,12,10,11,13,7,11,12,8,12,13,7,9,13]
def label : E → P := ![0,1,2,0,1,2,0,1,2,0,1,2,2,0,1,2,0,1,1,2,0]
def cot : Fin 8 → E := ![7,10,13,14,16,17,19,20]
def delta : S → ℤ × Nat := ![(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0)]
def tvBank : Array (Array B) := #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13],#[1,2,3,4,5,6,0,8,9,10,11,12,13,7],#[2,3,4,5,6,0,1,9,10,11,12,13,7,8],#[3,4,5,6,0,1,2,10,11,12,13,7,8,9],#[4,5,6,0,1,2,3,11,12,13,7,8,9,10],#[5,6,0,1,2,3,4,12,13,7,8,9,10,11],#[6,0,1,2,3,4,5,13,7,8,9,10,11,12]]
def teBank : Array (Array E) := #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20],#[3,4,5,6,7,8,9,10,11,13,14,12,15,16,17,19,20,18,1,2,0],#[6,7,8,9,10,11,13,14,12,16,17,15,19,20,18,2,0,1,4,5,3],#[9,10,11,13,14,12,16,17,15,20,18,19,2,0,1,5,3,4,7,8,6],#[13,14,12,16,17,15,20,18,19,0,1,2,5,3,4,8,6,7,10,11,9],#[16,17,15,20,18,19,0,1,2,3,4,5,8,6,7,11,9,10,14,12,13],#[20,18,19,0,1,2,3,4,5,6,7,8,11,9,10,12,13,14,17,15,16]]
def activeBank : Array (Array Bool) := #[#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]]
def tv (s : S) (b : B) : B := (tvBank[s.val]!)[b.val]!
def te (s : S) (e : E) : E := (teBank[s.val]!)[e.val]!
def active (s : S) (e : E) : Bool := (activeBank[s.val]!)[e.val]!
def chainBank : Array (Array (Array ℤ)) := #[#[],#[],#[#[-1,1,0,0,-1,1,1,-1,0,1,-1,0,1,0,-1,-1,1,0,0,0,0],#[0,0,0,0,-1,1,1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,1,-2,1,2,-1,-1,1,-1,0,0,0,0,-1,1,0,0,0,0],#[1,-1,0,0,-1,1,1,-1,0,1,-1,0,-1,0,1,1,-1,0,0,0,0],#[1,-1,0,1,-2,1,2,-1,-1,1,-1,0,-1,0,1,0,0,0,0,0,0],#[-1,1,0,0,0,0,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0]],#[#[-1,1,0,0,-1,1,1,-1,0,1,-1,0,1,0,-1,-1,1,0,0,0,0],#[0,0,0,0,-1,1,1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,1,-2,1,2,-1,-1,1,-1,0,0,0,0,-1,1,0,0,0,0],#[1,-1,0,0,-1,1,1,-1,0,1,-1,0,-1,0,1,1,-1,0,0,0,0],#[1,-1,0,1,-2,1,2,-1,-1,1,-1,0,-1,0,1,0,0,0,0,0,0],#[-1,1,0,0,0,0,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0]],#[],#[],#[#[0,0,0,-1,0,1,0,-1,1,1,-1,0,0,0,0,1,-1,0,0,0,0],#[0,0,0,0,-1,1,1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0]],#[#[-1,1,0,-1,0,1,0,-1,1,1,-1,0,1,0,-1,0,0,0,0,0,0],#[0,0,0,0,-1,1,1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,1,-1,0,1,0,-1,0,0,0,0,0,0,0,-1,1],#[1,-1,0,1,-1,0,2,-1,-1,1,0,-1,-1,0,1,0,0,0,0,-1,1],#[-1,1,0,-1,0,1,-1,0,1,0,-1,1,1,0,-1,0,0,0,0,1,-1],#[0,0,0,0,-1,1,0,0,0,0,-1,1,0,0,0,0,0,0,0,1,-1],#[-1,1,0,-1,1,0,-1,0,1,0,0,0,1,0,-1,0,0,0,0,0,0]],#[],#[],#[#[0,-1,1,1,-1,0,1,-1,0,0,-1,1,0,1,-1,0,1,-1,0,0,0],#[1,-1,0,1,-1,0,1,-1,0,1,-1,0,-1,1,0,0,0,0,0,0,0],#[0,-1,1,1,-1,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0],#[1,-1,0,1,-1,0,1,-1,0,1,0,-1,-1,0,1,0,-1,1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,1,0,1,-1,0,1,-1,0,0,0],#[1,0,-1,0,0,0,0,0,0,1,-1,0,-1,1,0,0,0,0,0,0,0],#[-1,0,1,0,0,0,0,0,0,-1,0,1,1,0,-1,0,1,-1,0,0,0]],#[#[-1,1,0,0,0,0,1,-1,0,1,0,-1,1,0,-1,-1,1,0,0,-1,1],#[0,0,0,0,0,0,1,-1,0,1,0,-1,0,0,0,0,0,0,0,-1,1],#[1,-1,0,0,0,0,1,-1,0,1,0,-1,-1,0,1,1,-1,0,0,-1,1],#[-1,1,0,0,0,0,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0]]]
def shiftsBank : Array (Array (Array S)) := #[#[],#[],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]],#[],#[],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]],#[],#[],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]],#[#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6],#[0,1,2,3,4,5,6]]]
def c (i j : Nat) : E → ℤ := fun e => ((chainBank[i]!)[j]!)[e.val]!
def move (i j k : Nat) : S := ((shiftsBank[i]!)[j]!)[k]!

instance (c0 : E → ℤ) : Decidable (Balanced src dst c0) := by
  unfold Balanced
  infer_instance

def Checked (i : Nat) : Prop :=
  ∀ j : Fin (D i).branches.length,
    let b := (D i).branches[j]
    Balanced src dst (c i j.val) ∧ (c i j.val) ∘ cot=b.diff ∧
    ∀ k : Fin b.added.length,
      push (te (move i j.val k.val)) (c i j.val) ∘ cot=b.added[k] ∧
      ∀ e : E, c i j.val e≠0 → active (move i j.val k.val) e = true
instance (i : Nat) : Decidable (Checked i) := by unfold Checked; infer_instance

private theorem cx0 : Checked 0 := by decide +kernel
private theorem cx1 : Checked 1 := by decide +kernel
private theorem cx2 : Checked 2 := by decide +kernel
private theorem cx3 : Checked 3 := by decide +kernel
private theorem cx4 : Checked 4 := by decide +kernel
private theorem cx5 : Checked 5 := by decide +kernel
private theorem cx6 : Checked 6 := by decide +kernel
private theorem cx7 : Checked 7 := by decide +kernel
private theorem cx8 : Checked 8 := by decide +kernel
private theorem cx9 : Checked 9 := by decide +kernel
private theorem cx10 : Checked 10 := by decide +kernel
private theorem cx11 : Checked 11 := by decide +kernel
theorem checked (i : Nat) (_hi : i ≤ 11) : Checked i := by
  by_cases h0_12 : i < 6
  · by_cases h0_6 : i < 3
    · by_cases h0_3 : i < 1
      · have e : i = 0 := by omega
        subst i
        exact cx0
      · by_cases h1_3 : i < 2
        · have e : i = 1 := by omega
          subst i
          exact cx1
        · have e : i = 2 := by omega
          subst i
          exact cx2
    · by_cases h3_6 : i < 4
      · have e : i = 3 := by omega
        subst i
        exact cx3
      · by_cases h4_6 : i < 5
        · have e : i = 4 := by omega
          subst i
          exact cx4
        · have e : i = 5 := by omega
          subst i
          exact cx5
  · by_cases h6_12 : i < 9
    · by_cases h6_9 : i < 7
      · have e : i = 6 := by omega
        subst i
        exact cx6
      · by_cases h7_9 : i < 8
        · have e : i = 7 := by omega
          subst i
          exact cx7
        · have e : i = 8 := by omega
          subst i
          exact cx8
    · by_cases h9_12 : i < 10
      · have e : i = 9 := by omega
        subst i
        exact cx9
      · by_cases h10_12 : i < 11
        · have e : i = 10 := by omega
          subst i
          exact cx10
        · have e : i = 11 := by omega
          subst i
          exact cx11

theorem edges_correct : ∀ e : E, (src e).val < 7 ∧ src e≠dst e ∧ next (src e) (label e)=dst e := by decide +kernel
theorem translated_incidence : ∀ s : S, ∀ e : E, active s e=true →
    src (te s e)=tv s (src e) ∧ dst (te s e)=tv s (dst e) ∧ label (te s e)=label e := by decide +kernel

theorem gauge_edges : ∀ e : E, ∀ k : Fin 8, gauge (src e) (dst e) k =
      if cot k=e then 1 else 0 := by decide +kernel

variable {A : Type*} [AddCommGroup A]

def laws (w : Fin 8 → A) : Prop :=
  ∀ s : S, ∃ ψ : A →+ A, ∃ p : B → A, ∀ e : E, active s e=true →
    normalized cot w (te s e)=ψ (normalized cot w e)+p (dst e)-p (src e)

theorem aug_sound (w : Fin 8 → A) (law : laws w)
    (i : Nat) (hi : i ≤ 11) (j : Fin (D i).branches.length)
    (zero : coeffMap w (D i).branches[j].diff=0) :
    Vanish (coeffMap w) (D i).branches[j].added := by
  intro z hz
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hz
  rw [←hk]
  obtain ⟨bal,d,aug⟩ := checked i hi j
  have info := aug k
  obtain ⟨ψ,p,H⟩ := law (move i j.val k.val)
  exact closure_of_chain src dst cot (c i j.val) bal _ w ψ p
    (fun e he => H e (info.2 e he)) _ _ d info.1 zero

theorem any_voltage (w : Fin 8 → A) (law : laws w) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarOrbitC7Voltage.HasCycle (coeffMap w) n :=
  HaarOrbitC7Data.any_voltage (coeffMap w) noTwo (aug_sound w law)

end HaarOrbitC7Checks
#print axioms HaarOrbitC7Checks.any_voltage
