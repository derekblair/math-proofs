import HaarOrbitCylinderData
import HaarOrbitChains
namespace HaarOrbitCylinderChecks
open HaarOrbitCylinderDAG HaarOrbitCylinderData HaarOrbitCylinderVoltage HaarOrbitChains HaarOrbitVoltage
set_option maxRecDepth 40000
set_option maxHeartbeats 0
abbrev E := Fin 45
abbrev S := Fin 12
def src : E → B := ![0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9,10,10,10,11,11,11,12,12,13,13,14,14,15,16,17]
def dst : E → B := ![18,21,25,19,22,26,20,23,24,21,24,28,22,25,29,23,26,27,24,27,31,25,28,32,26,29,30,27,30,34,28,31,35,29,32,33,30,33,31,34,32,35,33,34,35]
def label : E → P := ![0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,0,1,0,1,0,0,0]
def cot : Fin 10 → E := ![16,19,22,25,28,31,34,37,39,41]
def delta : S → ℤ × Nat := ![(0,0),(-1,0),(-1,1),(-1,2),(0,1),(0,2),(1,0),(1,1),(1,2),(-2,0),(-2,1),(-2,2)]
def tvBank : Array (Array B) := #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35],#[0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,0,0,0,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32],#[0,0,0,1,2,0,4,5,3,7,8,6,10,11,9,13,14,12,0,0,0,19,20,18,22,23,21,25,26,24,28,29,27,31,32,30],#[0,0,0,2,0,1,5,3,4,8,6,7,11,9,10,14,12,13,0,0,0,20,18,19,23,21,22,26,24,25,29,27,28,32,30,31],#[1,2,0,4,5,3,7,8,6,10,11,9,13,14,12,16,17,15,19,20,18,22,23,21,25,26,24,28,29,27,31,32,30,34,35,33],#[2,0,1,5,3,4,8,6,7,11,9,10,14,12,13,17,15,16,20,18,19,23,21,22,26,24,25,29,27,28,32,30,31,35,33,34],#[3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,0,0,0,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,0,0,0],#[4,5,3,7,8,6,10,11,9,13,14,12,16,17,15,0,0,0,22,23,21,25,26,24,28,29,27,31,32,30,34,35,33,0,0,0],#[5,3,4,8,6,7,11,9,10,14,12,13,17,15,16,0,0,0,23,21,22,26,24,25,29,27,28,32,30,31,35,33,34,0,0,0],#[0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,0,0,0,0,0,0,18,19,20,21,22,23,24,25,26,27,28,29],#[0,0,0,0,0,0,1,2,0,4,5,3,7,8,6,10,11,9,0,0,0,0,0,0,19,20,18,22,23,21,25,26,24,28,29,27],#[0,0,0,0,0,0,2,0,1,5,3,4,8,6,7,11,9,10,0,0,0,0,0,0,20,18,19,23,21,22,26,24,25,29,27,28]]
def teBank : Array (Array E) := #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44],#[0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31,33,34,36,38,40],#[0,0,0,0,0,0,0,0,0,3,4,5,6,7,8,0,1,2,12,13,14,15,16,17,9,10,11,21,22,23,24,25,26,18,19,20,30,31,33,34,27,28,38,40,36],#[0,0,0,0,0,0,0,0,0,6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14,24,25,26,18,19,20,21,22,23,33,34,27,28,30,31,40,36,38],#[3,4,5,6,7,8,0,1,2,12,13,14,15,16,17,9,10,11,21,22,23,24,25,26,18,19,20,30,31,32,33,34,35,27,28,29,38,39,40,41,36,37,43,44,42],#[6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14,24,25,26,18,19,20,21,22,23,33,34,35,27,28,29,30,31,32,40,41,36,37,38,39,44,42,43],#[9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,0,38,39,0,40,41,0,42,0,43,0,44,0,0,0,0],#[12,13,14,15,16,17,9,10,11,21,22,23,24,25,26,18,19,20,30,31,32,33,34,35,27,28,29,38,39,0,40,41,0,36,37,0,43,0,44,0,42,0,0,0,0],#[15,16,17,9,10,11,12,13,14,24,25,26,18,19,20,21,22,23,33,34,35,27,28,29,30,31,32,40,41,0,36,37,0,38,39,0,44,0,42,0,43,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,22,24,25,27,30,33],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,4,5,6,7,8,0,1,2,12,13,14,15,16,17,9,10,11,21,22,24,25,18,19,30,33,27],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14,24,25,18,19,21,22,33,27,30]]
def activeBank : Array (Array Bool) := #[#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,false,false,false],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,false,false,false],#[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,false,false,false],#[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true],#[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]]
def tv (s : S) (b : B) : B := (tvBank[s.val]!)[b.val]!
def te (s : S) (e : E) : E := (teBank[s.val]!)[e.val]!
def active (s : S) (e : E) : Bool := (activeBank[s.val]!)[e.val]!
def chainBank : Array (Array (Array ℤ)) := #[#[],#[#[0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,1,0,0,0,1,-1,0,1,-1,0,0,-1,1,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,1,0,0,0,1,-1,0,1,-1,0,0,0,0,1,-1,0,0,0,0,-1,0,1,1,-1,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0,0,0,0]],#[#[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,-1,0,0,-1,1,0,0,0,1,-1,0,0,0,0,0,-1,1,1,-1,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,1,0,0,0,1,-1,0,1,-1,0,0,0,0,1,-1,0,0,0,0,-1,0,1,1,-1,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0,0]],#[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,-1,0,0,-1,1,0,-1,1,1,-1,0,0,1,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,0,1,-1,0,-1,0,1,0,-1,1,1,-1,0,0,1,-1,0,0,0],#[0,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,-1,0,1,0,0,0,0,0,0,0,0,0,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0]],#[#[0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,1,0,0,0,1,-1,0,1,-1,0,0,-1,1,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,-1,1,0,-1,1,0,0,0,1,-1,0,1,-1,0,0,0,0,1,-1,0,0,0,0,-1,0,1,1,-1,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0,0,0,0]],#[],#[#[0,-1,1,0,0,0,0,0,0,1,-1,0,0,-1,1,0,0,0,1,-1,0,0,0,0,0,-1,1,1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,-1,1,0,0,0,0,0,0,1,-1,0,0,-1,1,0,0,0,1,-1,0,0,0,0,0,0,0,1,-1,0,0,0,0,-1,0,1,1,-1,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,1,0,0,0,0,0,0,1,0,-1,-1,1,0,0,0,0,0,0,0]]]
def shiftsBank : Array (Array (Array S)) := #[#[],#[#[0,1,2,3,4,5,6,7,8],#[0,1,2,3,4,5],#[0,9,10,11,1,2,3,4,5]],#[#[0,1,2,3,4,5],#[0,1,2,3,4,5],#[0,1,2,3,4,5,6,7,8]],#[#[0,9,10,11,1,2,3,4,5],#[0,1,2,3,4,5],#[0,1,2,3,4,5,6,7,8]],#[#[0,1,2,3,4,5,6,7,8],#[0,1,2,3,4,5],#[0,9,10,11,1,2,3,4,5]],#[],#[#[0,4,5,6,7,8],#[0,4,5],#[0,9,10,11,1,2,3,4,5]]]
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
theorem checked (i : Nat) (_hi : i ≤ 6) : Checked i := by
  by_cases h0_7 : i < 3
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
  · by_cases h3_7 : i < 5
    · by_cases h3_5 : i < 4
      · have e : i = 3 := by omega
        subst i
        exact cx3
      · have e : i = 4 := by omega
        subst i
        exact cx4
    · by_cases h5_7 : i < 6
      · have e : i = 5 := by omega
        subst i
        exact cx5
      · have e : i = 6 := by omega
        subst i
        exact cx6

theorem edges_correct : ∀ e : E, (src e).val < 18 ∧ src e≠dst e ∧ next (src e) (label e)=dst e := by decide +kernel
theorem translated_incidence : ∀ s : S, ∀ e : E, active s e=true →
    src (te s e)=tv s (src e) ∧ dst (te s e)=tv s (dst e) ∧ label (te s e)=label e := by decide +kernel

theorem gauge_edges : ∀ e : E, ∀ k : Fin 10, gauge (src e) (dst e) k =
      if cot k=e then 1 else 0 := by decide +kernel

variable {A : Type*} [AddCommGroup A]

def laws (w : Fin 10 → A) : Prop :=
  ∀ s : S, ∃ ψ : A →+ A, ∃ p : B → A, ∀ e : E, active s e=true →
    normalized cot w (te s e)=ψ (normalized cot w e)+p (dst e)-p (src e)

theorem aug_sound (w : Fin 10 → A) (law : laws w)
    (i : Nat) (hi : i ≤ 6) (j : Fin (D i).branches.length)
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

theorem any_voltage (w : Fin 10 → A) (law : laws w) (noTwo : ∀ a : A, a+a=0 → a=0) :
    ∃ n, n ∈ [4,8,16,32] ∧ HaarOrbitCylinderVoltage.HasCycle (coeffMap w) n :=
  HaarOrbitCylinderData.any_voltage (coeffMap w) noTwo (aug_sound w law)

end HaarOrbitCylinderChecks
#print axioms HaarOrbitCylinderChecks.any_voltage
