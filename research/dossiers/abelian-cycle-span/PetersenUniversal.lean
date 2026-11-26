import PetersenWalkData

namespace PetersenUniversal
open PetersenDecision PetersenWalkData GenericVoltage
open scoped BigOperators

variable {A : Type*} [AddCommGroup A]

def evaluation (W : Fin 10 → Fin 10 → A) : V →+ A where
  toFun u := ∑ k : Fin 15, u k • W (edges k).1 (edges k).2
  map_zero' := by simp
  map_add' u v := by
    change (∑ k : Fin 15, (u k+v k) • W (edges k).1 (edges k).2)
      = (∑ k : Fin 15, u k • W (edges k).1 (edges k).2) +
        (∑ k : Fin 15, v k • W (edges k).1 (edges k).2)
    simp only [add_zsmul,Finset.sum_add_distrib]

theorem evaluation_basis (W : Fin 10 → Fin 10 → A) (k : Fin 15) :
    evaluation W (evec k)=W (edges k).1 (edges k).2 := by
  change (∑ j : Fin 15, (if j=k then (1:ℤ) else 0) • W (edges j).1 (edges j).2)=_
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

set_option maxHeartbeats 0
set_option maxRecDepth 30000

theorem row_cycle (W : Fin 10 → Fin 10 → A) (anti : ∀ u v, W v u = -W u v)
    (j : Fin 15) (h0 : evaluation W (closing j)=0)
    (h1 : ∀ x∈clashes j, evaluation W x≠0) :
    Cycle (Adj base W) (size j) := by
  let E := evaluation W
  have start : E (pvec j 0)=0 := by rw [prefix_start,map_zero]
  have last : E (pvec j (size j))=0 := by
    rcases prefix_end j with h|h
    · rw [h]; exact h0
    · rw [h,map_neg]; change -(evaluation W (closing j))=0; simp [h0]
  let v (i : Fin (size j)) := vertex j i.val
  let P (i : Fin (size j)) := E (pvec j i.val)
  have adjStep (i : Fin (size j)) :
      base (v i) (v (cycSucc i)) ∧ P i+W (v i) (v (cycSucc i))=P (cycSucc i) := by
    have step := steps_complete j i
    unfold step_ok at step
    generalize e : etag j i.val = z at step
    rcases z with ⟨k,b⟩
    have vv : v (cycSucc i)=vertex j (i.val+1) := by
      change vertex j ((i.val+1)%size j)=vertex j (i.val+1)
      unfold vertex
      rw [Nat.mod_mod]
    have PP : P (cycSucc i)=E (pvec j (i.val+1)) := by
      change E (pvec j ((i.val+1)%size j))=_
      by_cases h : i.val+1<size j
      · rw [Nat.mod_eq_of_lt h]
      · have eq : i.val+1=size j := by omega
        rw [eq,Nat.mod_self,start,last]
    rw [vv,PP]
    change base (vertex j i.val) (vertex j (i.val+1)) ∧
      E (pvec j i.val)+W (vertex j i.val) (vertex j (i.val+1))=E (pvec j (i.val+1))
    cases b
    · have T := step.1
      simp only [Bool.false_eq_true,ite_false] at T
      refine ⟨⟨k,Or.inr T⟩,?_⟩
      rw [step.2,map_add]
      simp only [Bool.false_eq_true,ite_false,map_neg]
      change _ + W _ _ = _ + -(evaluation W (evec k))
      rw [evaluation_basis,T]
      exact congrArg (E (pvec j i.val) + ·) (anti _ _)
    · have T := step.1
      simp only [ite_true] at T
      refine ⟨⟨k,Or.inl T⟩,?_⟩
      rw [step.2,map_add]
      simp only [ite_true]
      change _ + W _ _ = _ + evaluation W (evec k)
      rw [evaluation_basis,T]
  apply lift_of_rows W v P (fun i => (adjStep i).1) (fun i => (adjStep i).2)
  intro i k ne eq pp
  have eq' : E (pvec j i.val)=E (pvec j k.val) := pp
  have bad := clashes_complete j i k ne eq
  rcases bad with H|H
  · apply h1 _ H
    change E _=0
    rw [map_sub,eq',sub_self]
  · apply h1 _ H
    change E _=0
    rw [map_sub,eq',sub_self]

theorem all_voltages (W : Fin 10 → Fin 10 → A) (anti : ∀ u v, W v u = -W u v) :
    ∃ n, (n=8 ∨ n=16) ∧ Cycle (Adj base W) n := by
  by_contra H
  apply chart_no_bad (evaluation W)
  intro j h0
  by_contra h1
  apply H
  refine ⟨size j,size_ok j,row_cycle W anti j h0 ?_⟩
  intro v hv hz
  exact h1 ⟨v,hv,hz⟩

theorem all_regular_covers {X : Type*} (C : RegularAbelianCover (Fin 10) A X base) :
    ∃ n, (n=8 ∨ n=16) ∧ Cycle C.adj n := by
  obtain ⟨n,h,c⟩ := all_voltages C.voltage C.voltage_antisymm
  exact ⟨n,h,C.cycle_transport c⟩

end PetersenUniversal
#print axioms PetersenUniversal.all_regular_covers
