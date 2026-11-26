import HaarDerivedBarbellCert

set_option maxRecDepth 4096

namespace HaarDerivedBarbell
open HaarDerivedWreathCore HaarDerivedWreathTrace HaarDerivedWreathAllFlow HaarSharpPortGeometry
open HaarAllNoncommuting

private abbrev V := Bool × W Q
private abbrev stepW := topStep x y
private def now : V := (false, 1)

private def walk : ℕ → V
  | 0 => now
  | n+1 => stepW (walk n) (code n)

private theorem proj_walk (n : ℕ) (hn : n ≤ 128) : proj (walk n) = base n := by
  induction n with
  | zero => exact base0.symm
  | succ n ih =>
    rw [walk,step_proj,ih (by omega)]
    exact (good_row n (by omega)).1.symm

private theorem light_walk (n : ℕ) (hn : n ≤ 128) (b : Bool) :
    (walk n).2.lamp (marker b).1 (marker b).2 = light n b := by
  induction n with
  | zero => exact (init_light b).symm
  | succ n ih =>
    rw [walk,step_flow,ih (by omega),proj_walk n (by omega)]
    exact ((good_row n (by omega)).2 b).symm

private def hW (a : V) : Bool × ℕ × ZMod 3 × ZMod 3 :=
  (a.1, HaarDerivedGirth22.key a.2.pos,
    a.2.lamp marker0.1 marker0.2, a.2.lamp marker1.1 marker1.2)

private theorem hWalk (i : Fin 128) : hW (walk i.val) = hash i := by
  change ((proj (walk i.val)).1, HaarDerivedGirth22.key (proj (walk i.val)).2,
      (walk i.val).2.lamp (marker false).1 (marker false).2,
      (walk i.val).2.lamp (marker true).1 (marker true).2) = _
  rw [proj_walk i.val (by omega), light_walk i.val (by omega) false, light_walk i.val (by omega) true]
  rfl

private theorem inj_walk : Function.Injective (fun i : Fin 128 => walk i.val) := by
  intro i j equal
  exact List.nodup_ofFn.mp good_nodup ((hWalk i).symm.trans ((congrArg hW equal).trans (hWalk j)))

private theorem fold_prefix (n : ℕ) (hn : n ≤ 128) :
    (tags.take n).foldl stepW now = walk n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : tags.length = 128 := by decide
    rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, ih (by omega)]
    change stepW (walk n) tags[n] = stepW (walk n) (code n)
    have hn' : n < tags.length := by omega
    simp [code,List.getElem?_eq_getElem hn'] <;> rfl

private def action (g : W Q) (a : V) : V := (a.1,g*a.2)

private theorem step_action (g : W Q) (a : V) (c : Fin 3) :
    stepW (action g a) c = action g (stepW a c) := by
  rcases a with ⟨p,a⟩
  simp [topStep,action,mul_assoc]

private theorem fold_action (w : List (Fin 3)) (g : W Q) (a : V) :
    w.foldl stepW (action g a) = action g (w.foldl stepW a) := by
  induction w generalizing a with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons,step_action,ih,List.foldl_cons]

private theorem step_twice (a : V) (c : Fin 3) : stepW (stepW a c) c = a := by
  rcases a with ⟨p,a⟩
  cases p <;> simp [topStep,oriented,mul_assoc]

private theorem fold_rev (w : List (Fin 3)) (a : V) :
    w.reverse.foldl stepW (w.foldl stepW a) = a := by
  induction w generalizing a with
  | nil => rfl
  | cons c cs ih => simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,step_twice]

private theorem closed_step (w : List (Fin 3)) (α z : W Q)
    (h : w.foldl stepW now = (false,α)) :
    w.foldl stepW (false,z) = (false,z*α) := by
  have he := fold_action w z now
  rw [h] at he
  simpa [action,now] using he

private theorem closed_rev (w : List (Fin 3)) (α z : W Q)
    (h : w.foldl stepW now = (false,α)) :
    w.reverse.foldl stepW (false,z) = (false,z*α⁻¹) := by
  have hv := fold_rev w now
  rw [h] at hv
  simpa [action,now,hv,mul_assoc] using (fold_action w.reverse (z*α⁻¹) (false,α))

private theorem projA : proj (A.foldl stepW now) = (false,(1:Q)) := by
  rw [← (show tags.take 22 = A by decide), fold_prefix 22 (by decide),proj_walk 22 (by decide),base22]

private theorem projAT : proj ((T.foldl stepW (A.foldl stepW now))) = (false,(1:Q)) := by
  rw [← List.foldl_append, ← (show tags.take 64 = A ++ T by decide), fold_prefix 64 (by decide),
    proj_walk 64 (by decide),base64]

private theorem projT : proj (T.foldl stepW now) = (false,(1:Q)) := by
  rw [fold_proj]
  have h := projAT
  rw [fold_proj, projA] at h
  exact h

private theorem full_close : walk 128 = now := by
  let α := (A.foldl stepW now).2
  let β := (T.foldl stepW now).2
  have ha : A.foldl stepW now = (false,α) := Prod.ext (congrArg (Prod.fst : Bool × Q → Bool) projA) rfl
  have hb : T.foldl stepW now = (false,β) := Prod.ext (congrArg (Prod.fst : Bool × Q → Bool) projT) rfl
  have hc : α*β=β*α :=
    ker_comm α β (congrArg Prod.snd projA) (congrArg Prod.snd projT)
  rw [← fold_prefix 128 (by decide), show tags.take 128 = tags by decide, tags]
  simp only [List.foldl_append]
  rw [ha, closed_step T β α hb, closed_rev A α (α*β) ha, closed_rev T β _ hb]
  change (false, α*β*α⁻¹*β⁻¹) = (false, 1)
  rw [hc]
  simp [mul_assoc]

private theorem adjacent_step (a : V) (c : Fin 3) :
    HaarCycle.haarAdj (up false x) (up true y) a (stepW a c) := by
  rcases a with ⟨p,a⟩
  cases p <;> fin_cases c <;>
    simp [HaarCycle.haarAdj, topStep,oriented,liftPort,mul_assoc]

/-- A 128-cycle in the mod-three wreath cover, certified by a projected
walk and two lamp coordinates. The full walk closes by a kernel commutator. -/
theorem cycle128 : HasCycle (up false x) (up true y) 128 := by
  refine ⟨fun i => walk i.val,inj_walk,?_⟩
  intro i
  have h := adjacent_step (walk i.val) (code i.val)
  change HaarCycle.haarAdj _ _ (walk i.val) (walk (i.val+1)) at h
  by_cases hp : i.val+1 < 128
  · simpa [Nat.mod_eq_of_lt hp] using h
  · have hf : i.val+1=128 := by omega
    rw [hf,full_close] at h
    simpa [hf,walk] using h

end HaarDerivedBarbell

#print axioms HaarDerivedBarbell.cycle128
