import NeutralAffine

namespace ScalarTrace

def eval (a : ℝ) : ℝ → List ℝ → ℝ
  | x, [] => x
  | x, c :: cs => eval a (a*x+c) cs

theorem eval_append (a x : ℝ) (cs ds : List ℝ) :
    eval a x (cs ++ ds) = eval a (eval a x cs) ds := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => exact ih (a*x+c)

theorem back (a x B C : ℝ) (ha : 1 < |a|) (hB : C ≤ (|a|-1)*B)
    (cs : List ℝ) (hc : ∀ c ∈ cs, |c| ≤ C) (hend : |eval a x cs| ≤ B) :
    |x| ≤ B := by
  induction cs generalizing x with
  | nil => exact hend
  | cons c cs ih =>
    exact NeutralAffine.expanding_bound a x c B C ha (hc _ (by simp)) hB
      (ih (a*x+c) (fun y hy => hc y (by simp [hy])) hend)

theorem forward (a x B C : ℝ) (ha : |a| < 1) (hB : C ≤ (1-|a|)*B)
    (cs : List ℝ) (hc : ∀ c ∈ cs, |c| ≤ C) (hx : |x| ≤ B) :
    |eval a x cs| ≤ B := by
  induction cs generalizing x with
  | nil => exact hx
  | cons c cs ih =>
    exact ih (a*x+c) (fun y hy => hc y (by simp [hy]))
      (NeutralAffine.contracting_bound a x c B C ha (hc _ (by simp)) hB hx)

theorem prefixes_back (a B C : ℝ) (ha : 1 < |a|) (hB : C ≤ (|a|-1)*B)
    (cs ds : List ℝ) (hc : ∀ c ∈ ds, |c| ≤ C)
    (hend : eval a 0 (cs ++ ds) = 0) (hpos : 0 ≤ B) :
    |eval a 0 cs| ≤ B := by
  apply back a _ B C ha hB ds hc
  rw [eval_append] at hend
  simpa [hend]

def zeval (s : ℤ) : ℤ → List ℤ → ℤ
  | z, [] => z
  | z, c :: cs => zeval s (s*z+c) cs

def labels (s q : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: cs => ((q*s)*c) :: labels s (q*s) cs

theorem fold_phase (s q z : ℤ) (hs : s*s=1) (cs : List ℤ) :
    (q*s^cs.length) * zeval s z cs = q*z + (labels s q cs).sum := by
  induction cs generalizing q z with
  | nil => simp [zeval,labels]
  | cons c cs ih =>
    have hp : q * s ^ (cs.length+1) = (q*s)*s^cs.length := by rw [pow_succ]; ring
    rw [List.length_cons, hp, zeval, ih, NeutralAffine.phase_step s q z c hs]
    simp [labels,add_assoc]

theorem unit_zero_iff (s : ℤ) (hs : s*s=1) (cs : List ℤ) :
    zeval s 0 cs = 0 ↔ (labels s 1 cs).sum = 0 := by
  have hh : (s^cs.length)*(s^cs.length) = 1 := by rw [← mul_pow, hs, one_pow]
  have hf := fold_phase s 1 0 hs cs
  simp at hf
  rw [← hf]
  exact (NeutralAffine.phase_zero _ _ hh).symm

end ScalarTrace

#print axioms ScalarTrace.prefixes_back
#print axioms ScalarTrace.forward
#print axioms ScalarTrace.unit_zero_iff
