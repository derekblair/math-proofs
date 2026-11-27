import HaarOrbitC7RealCover
import HaarOrbitC7DAG

namespace HeawoodCert
open HaarOrbitC7Voltage
open HaarOrbitC7DAG (linear Vanish map_linear)
structure Data where
  origin : B
  word : List P
  closing : V
  repeats : List V

def seed (d : Data) : State := (d.origin,0)

def atV (d : Data) (i : Fin d.word.length) : State :=
  (rows (seed d) d.word)[i.val]'(by simpa using i.isLt)

def check (d : Data) : Prop :=
  d.word.length ∈ [8,16,32] ∧
  (finish (seed d) d.word).1=(seed d).1 ∧
  (finish (seed d) d.word).2=d.closing ∧
  ∀ i j : Fin d.word.length, i.val<j.val →
    (atV d i).1=(atV d j).1 →
    ∃ k : Fin d.repeats.length,
      (atV d i).2-(atV d j).2=d.repeats[k] ∨
      (atV d i).2-(atV d j).2= -d.repeats[k]

instance (d : Data) : Decidable (check d) := inferInstanceAs (Decidable (_ ∧ _))

variable {A : Type*} [AddCommGroup A]

theorem from_seed (φ : V →+ A) (seed : State) (w : List P) (nonempty : 0<w.length)
    (cl : lift φ (finish seed w) = lift φ seed)
    (sep : ∀ i j : Fin w.length, i.val < j.val →
      lift φ ((rows seed w)[i.val]'(by simpa using i.isLt)) ≠
        lift φ ((rows seed w)[j.val]'(by simpa using j.isLt))) :
    HasCycle φ w.length := by
  let v (i : Fin w.length) := lift φ ((rows seed w)[i.val]'(by simpa using i.isLt))
  refine ⟨v,?_,?_⟩
  · intro i j eq
    rcases lt_trichotomy i.val j.val with h|h|h
    · exact False.elim (sep i j h eq)
    · exact Fin.ext h
    · exact False.elim (sep j i h eq.symm)
  · intro i
    by_cases h : i.val+1 < w.length
    · have H := rows_adj φ seed w i.val (by simpa using i.isLt) (by simpa using h)
      simpa [v,Nat.mod_eq_of_lt h] using H
    · have h' : i.val+1 = w.length := by omega
      have H := rows_final φ seed w i.val (by simpa using i.isLt) (by simpa using h')
      rw [cl] at H
      cases w with
      | nil => simp at nonempty
      | cons a w =>
        have z : (i.val+1)%(w.length+1)=0 := by rw [h',List.length_cons,Nat.mod_self]
        simpa [v,z,rows] using H


def NoCycles (φ : V →+ A) : Prop := ∀ n ∈ [8,16,32], ¬ HasCycle φ n

theorem force (φ : V →+ A) (F : NoCycles φ) (d : Data) (ok : check d)
    (h : ∀ v ∈ d.repeats, φ v ≠ 0) : φ d.closing≠0 := by
  rcases ok with ⟨len,clBase,clVec,pairs⟩
  intro e
  apply F _ len
  apply from_seed φ (seed d) d.word
  · simp at len
    omega
  · apply Prod.ext (show (lift φ (finish (seed d) d.word)).1=(lift φ (seed d)).1 from clBase)
    change φ (finish (seed d) d.word).2=φ (seed d).2
    rw [clVec]
    simpa [seed] using e
  · intro i j lt same
    obtain ⟨k,kc⟩ := pairs i j lt (congrArg (fun v : B × A => v.1) same)
    have z : φ ((atV d i).2-(atV d j).2)=0 := by
      rw [map_sub,sub_eq_zero]
      exact congrArg (fun v : B × A => v.2) same
    apply h _ (List.getElem_mem _)
    rcases kc with k'|k'
    · rwa [k'] at z
    · rwa [k',map_neg,neg_eq_zero] at z

theorem via_zero (φ : V →+ A) (rs : List V) (H : Vanish φ rs)
    (v : V) (cs : List ℤ) (e : v=linear rs cs) : φ v=0 := by
  rw [e,map_linear φ rs cs H]

theorem via_deps (φ : V →+ A) (rs : List V) (H : Vanish φ rs)
    (v w : V) (sgn : ℤ) (sgnOK : sgn=1 ∨ sgn= -1) (cs : List ℤ)
    (e : v=sgn • w + linear rs cs) (hw : φ w≠0) : φ v≠0 := by
  intro hv
  rw [e,map_add,map_zsmul,map_linear φ rs cs H,add_zero] at hv
  rcases sgnOK with rfl|rfl
  · exact hw (by simpa using hv)
  · exact hw (by simpa using hv)

theorem vanish_nil (φ : V →+ A) : Vanish φ [] := by simp [Vanish]
theorem vanish_one (φ : V →+ A) (v : V) (h : φ v=0) : Vanish φ [v] := by
  intro w hw
  have e : w=v := by simpa using hw
  rwa [e]
theorem vanish_two (φ : V →+ A) (v w : V) (h : φ v=0) (h' : φ w=0) :
    Vanish φ [v,w] := by
  intro u hu
  have e : u=v ∨ u=w := by simpa using hu
  rcases e with rfl|rfl <;> assumption

end HeawoodCert
#print axioms HeawoodCert.force
