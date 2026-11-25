import Complement
namespace QuadraticCA

def integ (x : Stream) : Stream
  | 0 => 0
  | i+1 => integ x i + x i

lemma d_integ (x : Stream) : d (integ x) = x := by
  ext i
  change integ x i + (integ x i + x i) = x i
  rw [←add_assoc,self_add,zero_add]
lemma integ_law (x : Stream) (i j : ℕ) :
    integ (fun t => d x (i+t)) j = x (i+j)+x i := by
  induction j with
  | zero => simpa [integ] using (self_add (x i)).symm
  | succ j ih =>
    rw [integ,ih]
    simp only [d]
    calc (x (i+j)+x i)+(x (i+j)+x (i+j+1)) =
        (x (i+j)+x (i+j))+(x (i+j+1)+x i) := by abel
      _ = _ := by rw [self_add,zero_add]; rfl

lemma integ_period {x : Stream} {n : ℕ} (h : Periodic n x) :
    Periodic (2*n) (integ x) := by
  have A (i : ℕ) : integ x (i+n) = integ x i + integ x n := by
    induction i with
    | zero => simp [integ]
    | succ i ih =>
      rw [show i+1+n = i+n+1 by omega]
      simp only [integ,ih,h i]; abel
  intro i
  rw [show i+2*n=(i+n)+n by omega,A,A,add_assoc,self_add,add_zero]

lemma function_phase {x : Stream} (i : ℕ) :
    (fun j : ℕ => x (i+j)) = (fun j => x (i+j)+x i) + (fun _ => x i) := by
  ext j; change x (i+j) = x (i+j)+x i+x i
  rw [add_assoc,self_add,add_zero]

def quotientCA (F : Stream → Stream) (x : Stream) : Stream :=
    d (F (integ x))

lemma complement_same_diff {F : Stream → Stream} (hc : ∀ x, F (x+1)=F x+1)
    {x y : Stream} (h : d x=d y) : d (F x)=d (F y) := by
  have e : d (x+y)=0 := by rw [d_add,h,stream_self]
  rcases const_zero_or_one e with H | H
  · rw [sum_eq_zero H]
  · have H' : x = y+1 := by
      have e := congrArg (· + y) H
      simpa [add_assoc, stream_self, add_comm (1 : Stream) y] using e
    rw [H',hc,d_add,d_one,add_zero]
lemma quotient_semiconj {F : Stream → Stream} (hc : ∀ x, F (x+1)=F x+1) (x : Stream) :
    quotientCA F (d x)=d (F x) :=
  complement_same_diff hc (d_integ (d x))

lemma quotient_proper {F : Stream → Stream}
    (hc : ∀ x, F (x+1)=F x+1) (h : Proper F) :
    Proper (quotientCA F) := by
  intro n hn x y hx hy he
  change d (F (integ x)) = d (F (integ y)) at he
  have e : d (F (integ x) + F (integ y)) = 0 := by rw [d_add,he,stream_self]
  have px := integ_period hx
  have py := integ_period hy
  rcases const_zero_or_one e with H | H
  · have z := h (2*n) (by omega) _ _ px py (sum_eq_zero H)
    simpa only [d_integ] using congrArg d z
  · have H' : F (integ x) = F (integ y)+1 := by
      have e := congrArg (· + F (integ y)) H
      simpa [add_assoc, stream_self, add_comm (1 : Stream) (F (integ y))] using e
    rw [←hc] at H'
    have z := h (2*n) (by omega) _ _ px (periodic_add py (periodic_one _)) H'
    simpa only [d_integ,d_add,d_one,add_zero] using congrArg d z

lemma polar_semiconj {F G : Stream → Stream} (H : ∀ x, G (d x)=d (F x)) (x y : Stream) :
    polar G (d x) (d y) = d (polar F x y) := by
  unfold polar
  rw [←d_add,H,H,H,←d_zero,H]
  repeat rw [d_add]
  rw [d_zero]

lemma quotient_quad {F : Stream → Stream} (hc : ∀ x, F (x+1)=F x+1) (hq : Quad F) :
    Quad (quotientCA F) := by
  intro x y z
  obtain ⟨a,ha⟩ : ∃ a, d a = x := ⟨integ x,d_integ x⟩
  obtain ⟨b,hb⟩ : ∃ b, d b = y := ⟨integ y,d_integ y⟩
  obtain ⟨c,hc'⟩ : ∃ c, d c = z := ⟨integ z,d_integ z⟩
  rw [←ha,←hb,←hc',←d_add]
  repeat rw [polar_semiconj (quotient_semiconj hc)]
  rw [hq,d_add]

lemma local_recenter {F : Stream → Stream} (h : Local F) (x : Stream) (i : ℕ) :
    F x i = F (fun j => x (i+j)) 0 := by
  obtain ⟨k,f,H⟩ := h
  rw [H,H]
  simp

lemma quotient_local {F : Stream → Stream} (h : Local F) (hc : ∀ x, F (x+1)=F x+1) :
    Local (quotientCA F) := by
  obtain ⟨k,f,H⟩ := h
  let e : (Fin (k+1) → K) → Stream := fun w j => if h : j<k+1 then w ⟨j,h⟩ else 0
  refine ⟨k+1, fun w => quotientCA F (e w) 0, ?_⟩
  intro x i
  let a := integ x
  let w := e (fun j => x (i+j.val))
  change d (F a) i = d (F (integ w)) 0
  have eqAt (l : ℕ) (hl : l≤1) :
      F a (i+l) = F (integ w) l + a i := by
    have head (j : ℕ) (hj : j<k+1) : integ w j = a (i+j)+a i := by
      have E : integ w j = integ (fun t => x (i+t)) j := by
        induction j with
        | zero => rfl
        | succ j ih =>
          simp only [integ, ih (by omega)]
          congr 1
          change (if h : j<k+1 then x (i+j) else 0) = x (i+j)
          rw [dite_eq_left (by omega)]
      rw [E]
      conv_lhs => arg 1; intro t; rw [←d_integ x]
      exact integ_law a i j
    let q : Stream := fun t => integ w t + a i
    have R : F a (i+l) = F q l := by
      rw [H,H]; congr 1; ext j
      have hlt : l+j.val<k+1 := by have := j.isLt; omega
      change a (i+l+j.val)=integ w (l+j.val)+a i
      rw [head _ hlt, add_assoc (a (i+(l+j.val))) (a i), self_add, add_zero, Nat.add_assoc]
    have C : ∀ u : K, u=0 ∨ u=1 := by decide
    rcases C (a i) with z | o
    · simpa [q,z] using R
    · have eqs : q = integ w+1 := by ext j; change integ w j+a i=integ w j+1; rw [o]
      rw [R,eqs,hc]
      change F (integ w) l+1=F (integ w) l+a i
      rw [o]
  change F a i + F a (i+1) = F (integ w) 0 + F (integ w) (0+1)
  have H0 : F a i = F (integ w) 0 + a i := by simpa using eqAt 0 (by decide)
  rw [H0,eqAt 1 (by decide)]
  calc (F (integ w) 0+a i)+(F (integ w) 1+a i) =
      (F (integ w) 0+F (integ w) 1)+(a i+a i) := by abel
    _ = _ := by rw [self_add,add_zero]

end QuadraticCA
