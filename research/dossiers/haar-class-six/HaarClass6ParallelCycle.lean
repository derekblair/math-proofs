import HaarClass6ParallelPairs

namespace HaarClass6ParallelCycle
open HaarClass6ParallelWords HaarClass6ParallelPairs HaarClass6ParallelSeparationCore
open HaarClass3Separation64 HaarClass5TemplateCycles HaarClass5TemplateClosure
open HaarUniversal36 HaarAllNoncommuting HaarClass4Ports HaarReducedWalkCycle
variable {G : Type*} [Group G]

theorem case_v (nil : L G 6=⊥) (odd : Odd (Nat.card G)) (x y : G)
    (nv : let f := QuotientGroup.mk' (L G 3); (portV (f x) (f y))^(3:ℕ) ≠ 1) :
    HasCycle x y 64 := by
  let S := L G 3
  let f := QuotientGroup.mk' S
  let X := f x
  let Y := f y
  have ni : L (G ⧸ S) 3=⊥ := quote_nil 3
  have oddQ : Odd (Nat.card (G ⧸ S)) := Odd.of_dvd_nat odd S.card_quotient_dvd_card
  have oddQQ := odd_projection oddQ
  have nC := project_c_cube ni X Y nv
  apply cycle_of_vertices x y W lenW (close nil x y)
  intro I J e
  have side := congrArg Prod.fst e
  change decide (I.val%2=1)=decide (J.val%2=1) at side
  have same : I.val%2=J.val%2 := by
    by_cases a : I.val%2=1 <;> by_cases b : J.val%2=1 <;> simp [a,b] at side <;> omega
  have h := congrArg (fun v : Bool × G => f v.2) e
  change f (path x y W I.val)=f (path x y W J.val) at h
  have pathE (u : Fin 64) : path X Y W u.val = HaarClass3Separation64.eval X Y (rowW u.val) :=
    path_matches ni X Y W rowW 64 zeroW (fun i h => stepsW ⟨i,h⟩) u.val (Nat.le_of_lt u.isLt)
  rw [map_path,map_path,pathE I,pathE J] at h
  let P := rowW I.val
  let Q := rowW J.val
  change HaarClass3Separation64.eval X Y P=HaarClass3Separation64.eval X Y Q at h
  obtain ⟨ei,ej,ek⟩ := two_layer X Y P Q h
  have pr := all_pairs I J
  change I=J ∨ I.val%2≠J.val%2 ∨ small3 (i P-i Q) ∨ small3 (j P-j Q) ∨
    (i P=i Q ∧ j P=j Q ∧ small3 (k P-k Q)) ∨
    (i P=i Q ∧ j P=j Q ∧ k P=k Q ∧ a P=a Q ∧ small3 (b Q-b P)) at pr
  rcases pr with he|he|he|he|⟨r,s,he⟩|⟨r,s,t,u,he⟩
  · exact he
  · exact (he same).elim
  · exact (pow_distinct oddQQ nC he ei).elim
  · exact (pow_distinct oddQQ nC he ej).elim
  · exact (pow_distinct oddQQ nC he (ek r s)).elim
  · have htail := tail_relation X Y ni P Q h r s t
    rw [u,sub_self,zpow_zero,one_mul] at htail
    have sep := pow_distinct oddQ nv (p:=b Q-b P) (q:=0) (by simpa only [sub_zero] using he)
    exact (sep (by simpa only [zpow_zero] using htail)).elim

end HaarClass6ParallelCycle
#print axioms HaarClass6ParallelCycle.case_v
