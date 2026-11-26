import HaarMetaS013OddCover

namespace HaarMetaS013RealCover
open HaarMetaS013Voltage
variable {A : Type*} [AddCommGroup A]

def Adj (W : B → B → A) (s t : B × A) : Prop :=
  s.1 ≠ t.1 ∧ ∃ j, next s.1 j = t.1 ∧ s.2 + W s.1 t.1 = t.2

def HasCycle (W : B → B → A) (n : Nat) : Prop :=
  ∃ v : Fin n → B × A, Function.Injective v ∧
    ∀ i, Adj W (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem real {n : Nat} (lo : 2≤n) (W : B → B → A)
    (C : HaarMetaS013Gauge.HasCycle W n) : HasCycle W n := by
  obtain ⟨v,vi,ce⟩ := C
  refine ⟨v,vi,fun i => ?_⟩
  let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have E : HaarMetaS013Gauge.adj W (v i) (v j) := ce i
  obtain ⟨k,hk,δ⟩ := E
  have finNe : i≠j := by
    intro h
    have e : i.val=(i.val+1)%n := congrArg Fin.val h
    by_cases b : i.val+1<n
    · rw [Nat.mod_eq_of_lt b] at e
      omega
    · have r : i.val+1=n := by omega
      rw [r,Nat.mod_self] at e
      omega
  have hn : (v i).1≠(v j).1 := by
    intro eq
    apply finNe
    apply vi
    refine Prod.ext eq ?_
    change (v i).2 + HaarMetaS013Gauge.clean W (v i).1 (v j).1 = (v j).2 at δ
    simpa [HaarMetaS013Gauge.clean,eq] using δ
  exact ⟨hn,k,hk,by simpa [HaarMetaS013Gauge.clean,hn] using δ⟩

theorem any_cover (W : B → B → A) (anti : ∀ u v, W v u = -W u v)
    (noTwo : ∀ a : A, a+a=0 → a=0) : ∃ n, n ∈ [4,8,16,32] ∧ HasCycle W n := by
  obtain ⟨n,h,C⟩ := HaarMetaS013OddCover.any_cover W anti noTwo
  refine ⟨n,h,real ?_ W C⟩
  simp at h
  omega

end HaarMetaS013RealCover
#print axioms HaarMetaS013RealCover.any_cover
