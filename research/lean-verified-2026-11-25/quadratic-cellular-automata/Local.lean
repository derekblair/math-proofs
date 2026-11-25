import Streams

namespace QuadraticCA

def polar (F : Stream → Stream) (x y : Stream) : Stream :=
  F (x+y) + F x + F y + F 0

def Quad (F : Stream → Stream) : Prop :=
  ∀ x y z, polar F (x+y) z = polar F x z + polar F y z

def Proper (F : Stream → Stream) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ x y, Periodic n x → Periodic n y → F x = F y → x = y

def Local (F : Stream → Stream) : Prop :=
  ∃ k : ℕ, ∃ f : (Fin k → K) → K, ∀ x i, F x i = f (fun j => x (i+j.val))

lemma stream_self (x : Stream) : x+x=0 := funext fun i => self_add (x i)
lemma sum_eq_zero {x y : Stream} (h : x+y=0) : x=y :=
  funext fun i => (add_eq_zero_iff _ _).1 (congrFun h i)

lemma polar_symm (F : Stream → Stream) (x y : Stream) :
    polar F x y = polar F y x := by
  unfold polar; rw [add_comm x y]; abel
lemma polar_zero (F : Stream → Stream) (y : Stream) : polar F 0 y = 0 := by
  unfold polar; rw [zero_add]
  calc F y + F 0 + F y + F 0 = (F y + F y) + (F 0 + F 0) := by abel
    _ = 0 := by simp [stream_self]
lemma polar_zero_right (F : Stream → Stream) (x : Stream) : polar F x 0 = 0 :=
  (polar_symm F x 0).trans (polar_zero F x)
lemma replay {F : Stream → Stream} (h : Local F) {x y : Stream} (i : ℕ)
    (e : ∀ j : ℕ, x (i+j) = y (i+j)) :
    F x i = F y i := by
  obtain ⟨k,f,H⟩ := h
  rw [H,H]
  congr 1
  ext j
  exact e j.val
lemma force_period {F : Stream → Stream} (h : Local F) {x : Stream}
    {n : ℕ} (e : Periodic n x) : Periodic n (F x) := by
  intro i
  obtain ⟨k,f,H⟩ := h
  rw [H,H]; congr 1; ext j
  rw [show i+n+j.val=i+j.val+n by omega, e]
lemma periodic_zero (n : ℕ) : Periodic n (0 : Stream) := fun _ => rfl
lemma periodic_one (n : ℕ) : Periodic n (1 : Stream) := fun _ => rfl
lemma periodic_add {n : ℕ} {x y : Stream} (hx : Periodic n x) (hy : Periodic n y) :
    Periodic n (x+y) := by
  intro i
  change x (i+n) + y (i+n) = x i + y i
  rw [hx,hy]
lemma polar_eventual {F : Stream → Stream} (h : Local F) (x y : Stream)
    (ey : EventuallyZero y) : EventuallyZero (polar F x y) := by
  obtain ⟨n,hn⟩ := ey
  refine ⟨n,fun i hi => ?_⟩
  have A : F (x+y) i = F x i :=
    replay h i (fun j => by change x (i+j)+y (i+j)=x (i+j); rw [hn _ (by omega),add_zero])
  have B : F y i = F 0 i := replay h i (fun j => hn _ (by omega))
  change F (x+y) i + F x i + F y i + F 0 i = 0
  rw [A,B,self_add,zero_add,self_add]
lemma ext_period_pw {k : ℕ} (v : Fin k → K) :
    ∃ e : ℕ, ∃ x : Stream, Periodic (2^e) x ∧ ∀ j : Fin k, x j.val = v j := by
  let N := 2^k
  have hn : k ≤ N := Nat.le_of_lt (Nat.lt_two_pow_self (n:=k))
  let X : Stream := fun i => if h : i%N<k then v ⟨i%N,h⟩ else 0
  refine ⟨k,X,?_,?_⟩
  · intro i
    dsimp only [X,N]
    rw [Nat.add_mod_right]
  · intro j
    have lt : j.val<N := lt_of_lt_of_le j.isLt hn
    simp [X,N,Nat.mod_eq_of_lt lt]
lemma constant_outputs {F : Stream → Stream} (h : Local F) (hp : Proper F) :
    F 0 + F 1 = 1 := by
  obtain ⟨k,f,H⟩ := h
  have const0 (i : ℕ) : F 0 i = F 0 0 := by rw [H,H]; rfl
  have const1 (i : ℕ) : F 1 i = F 1 0 := by rw [H,H]; rfl
  have ne : F 0 0 ≠ F 1 0 := by
    intro eq
    have fEq : F 0 = F 1 := funext fun i => (const0 i).trans (eq.trans (const1 i).symm)
    have z1 := hp 1 (by decide) 0 1 (periodic_zero 1) (periodic_one 1) fEq
    exact (zero_ne_one (α:=K)) (congrFun z1 0)
  ext i
  change F 0 i + F 1 i = 1
  rw [const0,const1]
  have H' : ∀ a b : K, a ≠ b → a+b=1 := by decide
  exact H' _ _ ne

end QuadraticCA
