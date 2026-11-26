import HeawoodLift64Embed

namespace HeawoodLift64
open HaarOrbitC7Voltage (B P next)
open HomologyThree HaarDerivedFlowPositive
open scoped BigOperators

set_option maxRecDepth 30000
set_option maxHeartbeats 0

private def label (i : ℕ) : P := tags[i]?.getD 0
private def opp (i : Fin 64) : Fin 64 := ⟨mates[i.val]?.getD 0 |>.mod 64, Nat.mod_lt _ (by decide)⟩
private theorem opp_twice (i : Fin 64) : opp (opp i)=i := by decide +revert
private def opposite : Equiv.Perm (Fin 64) := ⟨opp,opp,opp_twice,opp_twice⟩

private theorem opposite_pair (i : Fin 64) :
    (raw (opp i).val, raw ((opp i).val+1)) = (raw (i.val+1),raw i.val) := by decide +revert

private def light (i : ℕ) : Fin 2 → Z := lamps[i]?.getD 0
private def hash (i : Fin 64) : Compact × (Fin 2 → Z) := (raw i.val, light i.val)
private theorem hash_nodup : (List.ofFn hash).Nodup := by decide
private theorem light0 : ∀ j, light 0 j = 0 := by decide
private theorem raw_close : raw 64 = raw 0 := by decide

private def Good (i : ℕ) : Prop :=
  step (raw i) (label i) = raw (i+1) ∧
    ∀ j : Fin 2, light (i+1) j = light i j + bump (raw i) (raw (i+1)) (marks j)

private instance (i : ℕ) : Decidable (Good i) := by unfold Good; infer_instance
private theorem all_good (i : Fin 64) : Good i.val := by decide +revert

private def phase (n : ℕ) : Lamp Compact :=
  fun q => ∑ i : Fin n, bump (raw i.val) (raw (i.val+1)) q

private theorem phase0 : phase 0 = 0 := by
  funext q
  simp [phase]

private theorem phase_next (n : ℕ) :
    phase (n+1) = phase n + bump (raw n) (raw (n+1)) := by
  funext q
  simp [phase,Fin.sum_univ_castSucc]

private theorem lamp_eq (i : ℕ) (hi : i ≤ 64) (j : Fin 2) :
    phase i (marks j) = light i j := by
  induction i with
  | zero => rw [phase0,light0]; rfl
  | succ i ih =>
    rw [phase_next,Pi.add_apply,ih (by omega)]
    exact ((all_good ⟨i,by omega⟩).2 j).symm

private theorem phase_close : phase 64 = 0 := by
  funext q
  let F (i : Fin 64) := bump (raw i.val) (raw (i.val+1)) q
  have anti (i : Fin 64) : F (opposite i) = -F i := by
    change bump (raw (opp i).val) (raw ((opp i).val+1)) q = _
    have e := opposite_pair i
    have e₁ : raw (opp i).val = raw (i.val+1) := congrArg Prod.fst e
    have e₂ : raw ((opp i).val+1) = raw i.val := congrArg Prod.snd e
    rw [e₁, e₂]
    simp only [F,bump]
    abel
  have e : ∑ i, F (opposite i) = ∑ i, F i := Equiv.sum_comp opposite F
  simp only [anti,Finset.sum_neg_distrib] at e
  have h : (∑ i, F i) * (2 : Z) = 0 := by
    linear_combination -e
  exact (mul_eq_zero.mp h).resolve_right (by decide)

private def high (i : ℕ) : Compact × Lamp Compact := (raw i, phase i)
private theorem high_close : high 64 = high 0 := Prod.ext raw_close (phase_close.trans phase0.symm)

private theorem high_inj : Function.Injective (fun i : Fin 64 => high i.val) := by
  let read (a : Compact × Lamp Compact) : Compact × (Fin 2 → Z) :=
    (a.1, fun j => a.2 (marks j))
  have E (i : Fin 64) : read (high i.val) = hash i :=
    Prod.ext rfl (funext (lamp_eq i.val i.isLt.le))
  intro i j h
  exact List.nodup_ofFn.mp hash_nodup ((E i).symm.trans ((congrArg read h).trans (E j)))

private theorem high_step (i : Fin 64) : liftEdge smallEdge (high i.val) (high (i.val+1)) :=
  ⟨⟨label i.val,(all_good i).1⟩,(phase_next i.val).symm⟩

/-- The full ordered-edge second mod-three homology cover of Heawood has a
simple cycle of length 64. No group action or Haar structure is assumed. -/
theorem cycle64 : Cyclic Double 64 := by
  refine ⟨fun i => lift₂ (high i.val),lift₂_inj.comp high_inj, ?_⟩
  intro i
  apply lift₂_adj
  change liftEdge smallEdge (high i.val) (high ((i.val+1)%64))
  by_cases h : i.val+1 < 64
  · rw [Nat.mod_eq_of_lt h]
    exact high_step i
  · have e : i.val+1=64 := by omega
    rw [e, Nat.mod_self, ← high_close]
    simpa [e] using high_step i

end HeawoodLift64

#print axioms HeawoodLift64.cycle64
