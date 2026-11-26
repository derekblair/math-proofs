import HaarDerivedModThree

namespace HaarDerivedCoverTransfer
open HaarDerivedFlowPositive HaarDerivedModThree
variable {V W : Type*} [Fintype W] [DecidableEq W]

def periodicLift (n : Nat) (h : 0<n) (v : Fin n → V) (i : Nat) : V :=
  v ⟨i%n,Nat.mod_lt _ h⟩

theorem periodic (n : Nat) (h : 0<n) (v : Fin n → V) (i : Nat) :
    periodicLift n h v (i+n)=periodicLift n h v i := by
  unfold periodicLift
  apply congrArg v
  apply Fin.ext
  exact Nat.add_mod_right _ _

theorem nat_edge {n : Nat} (hn : 0<n) (C : V → V → Prop)
    (v : Fin n → V)
    (edge : ∀ i, C (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩)) (i : Nat) :
    C (periodicLift n hn v i) (periodicLift n hn v (i+1)) := by
  let t : Fin n := ⟨i%n,Nat.mod_lt _ hn⟩
  have E : (⟨(t.val+1)%n,Nat.mod_lt _ hn⟩ : Fin n) = ⟨(i+1)%n,Nat.mod_lt _ hn⟩ := by
    apply Fin.ext
    change (i%n+1)%n=(i+1)%n
    rw [Nat.add_mod (i%n),Nat.mod_mod,Nat.add_mod i]
  have h := edge t
  rw [E] at h
  exact h

theorem bound_of_cycle {n : Nat} (hn : 3≤n) (h : Nat) (π : V → W)
    (C : V → V → Prop) (R : W → W → Prop)
    (symmetricC : ∀ {u v}, C u v → C v u)
    (symm : ∀ {u v}, R u v → R v u) (loop : ∀ w, ¬ R w w)
    (edge_map : ∀ {u v}, C u v → R (π u) (π v))
    (locally_inj : ∀ {a b c}, C a b → C a c → π b=π c → b=c)
    (girth : ∀ k, 3≤k → Cyclic R k → 2*h≤k)
    (v : Fin n → V) (inj : Function.Injective v)
    (edge : ∀ i, C (v i) (v ⟨(i.val+1)%n,Nat.mod_lt _ (by omega)⟩))
    (div : ∀ u w, (3:ℤ) ∣ flow (fun i => π (periodicLift n (by omega) v i)) n u w) :
    3*(2*h)≤n := by
  let a := periodicLift n (by omega) v
  let b := π ∘ a
  have e := nat_edge (by omega : 0<n) C v edge
  have per := periodic n (by omega : 0<n) v
  have bounce (i : Nat) : b (i+2)≠b i := by
    intro y
    have E : a (i+2)=a i := locally_inj (e (i+1)) (symmetricC (e i)) y
    have mod : (i+2)%n=i%n := congrArg Fin.val (inj E)
    have n2 : 2<n := by omega
    have d := Nat.add_mod i 2 n
    rw [Nat.mod_eq_of_lt n2,mod] at d
    have nn : (i%n)<n := Nat.mod_lt _ (by omega)
    by_cases B : i%n+2<n
    · rw [Nat.mod_eq_of_lt B] at d
      omega
    · have s : (i%n+2)%n=i%n+2-n := Nat.mod_eq_sub_mod (by omega) |>.trans
        (Nat.mod_eq_of_lt (by omega))
      rw [s] at d
      omega
  exact length_bound b n h (by omega) R (fun i => edge_map (e i))
    loop symm girth (fun i => congrArg π (per i)) bounce div

end HaarDerivedCoverTransfer
#print axioms HaarDerivedCoverTransfer.bound_of_cycle
