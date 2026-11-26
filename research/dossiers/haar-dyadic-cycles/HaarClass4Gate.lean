import HaarClass4Certificates

namespace HaarClass4Gate
open HaarClass4CollectCore HaarClass4Powers HaarClass4Normal HaarClass4Table HaarClass4Projection HaarClass4Certificates HaarAllNoncommuting

variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem left_power (c x u A : G) (hcu : Commute c u) (hA : Central A)
    (cx : c*x=x*c*(u*A)) (ux : u*x=x*u*A) (k : ℤ) :
    c^k*x = u^k*x*c^k := by
  rw [HaarCycle.shift c x (u*A) (hcu.symm.mul_left (hA c)) cx k,
    HaarCycle.shift u x A (hA u) ux k,(hA u).symm.mul_zpow k]
  simp only [mul_assoc]
  rw [((hA c).zpow_zpow k k).eq, ← mul_assoc (u^k) (c^k),(hcu.zpow_zpow k k).eq.symm]
  simp only [mul_assoc]

theorem central_extend (W S y D : G) (hS : Central S) (hD : Central D)
    (h : W*y=y*W*D) : (W*S)*y = D*(y*(W*S)) := by
  calc
    (W*S)*y = (W*y)*S := by simp only [mul_assoc]; rw [(hS y).eq]
    _ = (y*W)*D*S := by rw [h]
    _ = D*(y*(W*S)) := by
      rw [← (hD (y*W)).eq]
      simp only [mul_assoc]

theorem first_cubes (M : Data G) (F : M.c^3=M.u*M.v) :
    M.u^3=M.a*M.b ∧ M.v^3=M.b*M.d := by
  have X₀ := left_power M.c M.x M.u M.a M.hcu M.ca M.cx M.ux 3
  have Y₀ := left_power M.c M.y M.v M.d M.hcv M.cd M.cy M.vy 3
  simp only [zpow_ofNat] at X₀ Y₀
  rw [F] at X₀ Y₀
  have zx := move_right M.x M.c M.u M.v M.a M.b M.hcu M.ca M.cb M.cx M.ux M.vx 0 1 1
  have zy := move_right_y M.y M.c M.u M.v M.b M.d M.hcv M.huv M.cb M.cd M.cy M.uy M.vy 0 1 1
  have X : (M.u*M.v)*M.x=M.x*(M.u*M.v)*(M.a*M.b) := by simpa using zx
  have Y : (M.u*M.v)*M.y=M.y*(M.u*M.v)*(M.b*M.d) := by simpa using zy
  have X' := central_extend _ 1 _ _ (fun g => Commute.one_left g) (central_mul M.ca M.cb) X
  have Y' := central_extend _ 1 _ _ (fun g => Commute.one_left g) (central_mul M.cb M.cd) Y
  have XX : (M.u*M.v)*M.x=(M.a*M.b)*(M.x*(M.u*M.v)) := by simpa only [mul_one] using X'
  have YY : (M.u*M.v)*M.y=(M.b*M.d)*(M.y*(M.u*M.v)) := by simpa only [mul_one] using Y'
  exact ⟨mul_right_cancel (by rw [← mul_assoc,←X₀,XX]),
    mul_right_cancel (by rw [← mul_assoc,←Y₀,YY])⟩

theorem cube_center (x u A : G) (hA : Central A) (ux : u*x=x*u*A)
    (U : Central (u^3)) : A^3=1 := by
  have e := HaarCycle.shift u x A (hA u) ux 3
  simp only [zpow_ofNat] at e
  rw [(U x).eq] at e
  exact (mul_left_cancel (a:=x*u^3) (by simpa using e : (x*u^3)*1=(x*u^3)*A^3)).symm

theorem first_is_one (M : Data G) : eval M unstable=1 ↔ M.c^3=M.u*M.v := by
  have e : eval M unstable=(M.c^3)⁻¹*(M.u*M.v) := by
    norm_num [eval,unstable,mid,tail,zpow_neg,mul_assoc]
  rw [e,inv_mul_eq_one,eq_comm]

theorem second_relation (M : Data G) (F' : eval M unstable'=1) :
    M.c^3=M.u*M.v^4*M.b⁻¹*M.d⁻¹ := by
  have e : eval M unstable'=(M.c^3)⁻¹*(M.u*M.v^4*M.b⁻¹*M.d⁻¹) := by
    norm_num [eval,unstable',mid,tail,zpow_neg,mul_assoc]
  rw [e,inv_mul_eq_one] at F'
  exact F'

theorem second_implies_first (M : Data G) (F' : eval M unstable'=1) :
    M.c^3=M.u*M.v := by
  let T := M.u*M.v^4*M.b⁻¹*M.d⁻¹
  let J := M.b*M.d^4
  have Rel : M.c^3=T := second_relation M F'
  have L₀ := left_power M.c M.y M.v M.d M.hcv M.cd M.cy M.vy 3
  have L : T*M.y=M.v^3*(M.y*T) := by
    simp only [zpow_ofNat] at L₀
    rw [Rel] at L₀
    simpa only [mul_assoc] using L₀
  have c₁ : Central (M.b⁻¹*M.d⁻¹) :=
    central_mul (fun z => (M.cb z).inv_left) (fun z => (M.cd z).inv_left)
  have c₂ : Central J := central_mul M.cb (fun z => (M.cd z).pow_left 4)
  have z := move_right_y M.y M.c M.u M.v M.b M.d M.hcv M.huv M.cb M.cd M.cy M.uy M.vy 0 1 4
  have h : (M.u*M.v^4)*M.y=M.y*(M.u*M.v^4)*J := by simpa [J] using z
  have R : T*M.y=J*(M.y*T) := by
    simpa only [T,mul_assoc] using central_extend _ _ _ _ c₁ c₂ h
  have v3 : M.v^3=J := mul_right_cancel (L.symm.trans R)
  have cent : Central (M.v^3) := v3.symm ▸ c₂
  have d3 := cube_center M.y M.v M.d M.cd M.vy cent
  have v3' : M.v^3=M.b*M.d := by
    rw [v3]
    unfold J
    rw [show (4:ℕ)=3+1 by decide,pow_succ,d3,one_mul]
  calc
    M.c^3 = M.u*M.v^4*M.b⁻¹*M.d⁻¹ := second_relation M F'
    _ = M.u*M.v := by
      rw [show (4:ℕ)=1+3 by decide,pow_add,pow_one,v3']
      have hz : (M.b*M.d)*M.b⁻¹*M.d⁻¹=1 := by
        rw [mul_assoc M.b M.d,(M.cd M.b⁻¹).eq]
        group
      simpa only [mul_assoc,mul_one] using congrArg (fun z => M.u*M.v*z) hz

theorem certificate (M : Data G) (φ : G →* H) (ψ : G →* K)
    (hφ : KillsMid M φ) (hψ : KillsTail M ψ)
    (ord : ∀ n : ℤ, small n → (φ M.c)^n ≠ 1)
    (ord3 : ∀ n : ℤ, n%3≠0 → (φ M.c)^n ≠ 1)
    (deep : ψ M.u≠1) : HasCycle M.x M.y 32 := by
  by_cases F : M.c^3=M.u*M.v
  · have h := (first_cubes M F).1
    have c : Central (M.u^3) := h.symm ▸ central_mul M.ca M.cb
    exact conditional_simple M φ hφ ord3 F h (cube_center M.x M.u M.a M.ca M.ux c)
  · exact ordinary_simple M φ ψ hφ hψ ord deep
      (fun h => F ((first_is_one M).mp h)) (fun h => F (second_implies_first M h))

end HaarClass4Gate

#print axioms HaarClass4Gate.certificate
