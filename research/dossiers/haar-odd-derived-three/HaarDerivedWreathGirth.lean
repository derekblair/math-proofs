import HaarDerivedWreathIndicator

namespace HaarDerivedWreathGirth
open HaarDerivedWreathCore HaarDerivedWreathTrace HaarDerivedHaarTransfer
open HaarDerivedCoverTransfer HaarDerivedModThree
open HaarCycle HaarAllNoncommuting
open HaarHalfCollision (branch symmetric port)
open HaarSharpPortGeometry (oriented)
variable {Q : Type*} [Group Q] [DecidableEq Q]

theorem girth_bound [Finite Q] (x y : Q) (hx : x≠1) (hy : y≠1) (hxy : x≠y) (h : Nat)
    (base : ∀ k, 3≤k → HasCycle x y k → 2*h≤k)
    (n : Nat) (n3 : 3≤n)
    (lifted : HasCycle (liftPort x y 1) (liftPort x y 2) n) :
    3*(2*h)≤n := by
  letI : Fintype Q := Fintype.ofFinite Q
  obtain ⟨v,vi,ve⟩ := lifted
  let t := periodicLift n (by omega) v
  let a := trace (π : W Q→*Q) (by omega) v
  have tr (i : Nat) : a i=proj (t i) := rfl
  suffices D : ∀ r j, j≠0 → (3:ℤ) ∣ flow a n (false,r) (step x y (false,r) j) by
    apply bound_of_haar_cycle (π : W Q→*Q) (liftPort x y 1) (liftPort x y 2)
      (by simpa [basePort] using hx) (by simpa [basePort] using hy)
      (by simpa [basePort] using hxy) n3 h (by simpa [basePort] using base) v vi ve
    intro u w ed nmatch
    have ed' : haarAdj x y u w := by simpa [basePort] using ed
    cases b : u.1
    · obtain ⟨ws,j,e⟩ := branch x y u w ed'
      have posit : u=(false,u.2) := Prod.ext b rfl
      have H : w=step x y (false,u.2) j := by
        apply Prod.ext
        · simpa [step,b] using ws
        · simpa [b,step,oriented,basePort,port] using e
      have nj : j≠0 := by
        intro J; subst j
        exact nmatch (by simpa [b,port] using e.symm)
      rw [posit,H]
      exact D _ _ nj
    · have ww : w.1=false := by simpa [b] using (branch x y u w ed').1
      obtain ⟨us,j,e⟩ := branch x y w u (symmetric x y ed')
      have ww' : w=(false,w.2) := Prod.ext ww rfl
      have H : u=step x y (false,w.2) j := by
        apply Prod.ext
        · simpa [step,ww] using us
        · simpa [ww,step,oriented,basePort,port] using e
      have nj : j≠0 := by
        intro J; subst j
        exact nmatch (by simpa [ww,port] using e)
      have expr : flow a n u w = -flow a n w u := by simp [flow,neg_sub]
      rw [expr,ww',H]
      exact dvd_neg.mpr (D _ _ nj)
  intro r j nj
  let L (i : Nat) := (t i).2.lamp (decide (j=2)) r
  apply div_of_lamp_update a n (false,r) (step x y (false,r) j) L
  · have P := periodic n (by omega : 0<n) v 0
    simpa only [L,t,Nat.zero_add] using congrArg (fun q : Bool × W Q => q.2.lamp (decide (j=2)) r) P
  · intro i _
    have E := nat_edge (by omega : 0<n) (haarAdj (liftPort x y 1) (liftPort x y 2)) v ve i
    obtain ⟨c,ce⟩ := top_edge x y E
    have ce' : topStep x y (t i) c=t (i+1) := ce
    have M := step_flow x y (t i) c (decide (j=2)) r
    rw [ce',edgeFlow_indicator x y hx hy hxy r j nj] at M
    have pp : step x y (a i) c = a (i+1) := by rw [tr,tr,← step_proj,ce']
    simpa [L,←tr,pp] using M

end HaarDerivedWreathGirth
#print axioms HaarDerivedWreathGirth.girth_bound
