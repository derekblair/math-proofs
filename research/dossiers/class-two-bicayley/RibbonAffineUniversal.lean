import RibbonAffineUniversalCheck

namespace RibbonAffine.Universal

variable {K : Type*} [Field K]

private theorem strip {t : Kˣ} (odd : Odd (orderOf t)) {E : ℤ} {s d : ℕ}
    (h : E.natAbs=2^s*d) (e : t^E=1) : t^d=1 := by
  have N : orderOf t ∣ E.natAbs := by
    have Z := orderOf_dvd_iff_zpow_eq_one.mpr e
    have H := Int.natAbs_dvd_natAbs.mpr Z
    simpa using H
  rw [h] at N
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact ((Nat.coprime_two_right.mpr odd).pow_right s).dvd_of_dvd_mul_left N

private theorem multiplier (t : Kˣ) (B : Branch) (i j : Fin 32)
    (e : (eRow (t^B.v) (t^(-B.u)) (position B.word i.val)).2.1 =
      (eRow (t^B.v) (t^(-B.u)) (position B.word j.val)).2.1) :
    t^(expDelta B i j)=1 := by
  let I := position B.word i.val
  let J := position B.word j.val
  change (t^B.v)^I.i * (t^(-B.u))^I.j = (t^B.v)^J.i * (t^(-B.u))^J.j at e
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add] at e
  have H : expDelta B i j = (B.v*I.i + (-B.u)*I.j) - (B.v*J.i + (-B.u)*J.j) := by
    change (I.i-J.i)*B.v - (I.j-J.j)*B.u = _
    ring
  rw [H,zpow_sub,e,mul_inv_cancel]

private theorem translation (t : Kˣ) (B : Branch) (i j : Fin 32)
    (e : (eRow (t^B.v) (t^(-B.u)) (position B.word i.val)).2.2 =
      (eRow (t^B.v) (t^(-B.u)) (position B.word j.val)).2.2) :
    pl t 1 (trDelta B i j)=0 := by
  rw [trDelta,← sub_sound,pl_append,negative_sound]
  change pl (t^B.v) (t^(-B.u)) (position B.word i.val).tr =
    pl (t^B.v) (t^(-B.u)) (position B.word j.val).tr at e
  rw [e,add_neg_cancel]

private theorem m_zero (t : Kˣ) (n : ℕ) (h : t^n=1) : pl t 1 (mulDelta n)=0 := by
  simp [mulDelta,pl,mon,zpow_natCast,h]

theorem separates (q : Fin 14) (t : Kˣ) (odd : Odd (orderOf t))
    (root : pl t 1 (branch q).f=0) (nonzero : ((branch q).constant : K)≠0)
    (i j : Fin 32) (l : i.val<j.val) :
    eRow (t^(branch q).v) (t^(-(branch q).u)) (position (branch q).word i.val) ≠
      eRow (t^(branch q).v) (t^(-(branch q).u)) (position (branch q).word j.val) := by
  intro e
  let B := branch q
  let C := cert q i j
  change pl t 1 B.f = 0 at root
  have E := table_valid q i j l
  rcases E with S | ⟨ex,div,ident⟩
  · exact S (congrArg Prod.fst e)
  · have m := m_zero t C.d (strip odd ex (multiplier t B i j (congrArg (fun x => x.2.1) e)))
    have d := translation t B i j (congrArg (fun x => x.2.2) e)
    have k := poly_eq t 1 _ _ ident
    change pl t 1 (combination B C i j) = pl t 1 [(0,0,C.k)] at k
    simp only [combination,pl_append,pl_mul,root,d,m,mul_zero,add_zero] at k
    have kc : (C.k : K)=0 := by simpa [pl,mon] using k.symm
    obtain ⟨n,hn⟩ := div
    apply nonzero
    change (B.constant : K)=0
    rw [hn,Nat.cast_mul,kc,zero_mul]

end RibbonAffine.Universal
#print axioms RibbonAffine.Universal.separates
