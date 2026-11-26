import HaarDerivedFlowPositive
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace HaarDerivedReflect
variable {V : Type*} (R : V → V → Prop)

theorem reverse_forces_branch (s : Nat → V) (j : Nat)
    (edges : ∀ i, R (s i) (s (i+1)))
    (loop : ∀ u, ¬R u u) (symm : ∀ {u v}, R u v → R v u)
    (noBounce : ∀ i, s (i+2)≠s i) (r0 : s (j+1)=s 0) (r1 : s j=s 1) :
    ∃ b, ∃ a : Fin 3 → V, Function.Injective a ∧ ∀ i, R b (a i) := by
  classical
  by_contra H
  have unique (b a c d : V) (e1 : R b a) (e2 : R b c) (e3 : R b d)
      (ac : c≠a) (ad : d≠a) : c=d := by
    by_contra h
    apply H
    let W : Fin 3 → V := ![a,c,d]
    refine ⟨b,W,?_,?_⟩
    · intro m n q
      fin_cases m <;> fin_cases n <;> simp_all [W]
    · intro m
      fin_cases m
      · exact e1
      · exact e2
      · exact e3
  have mirror : ∀ k, k≤j → s k=s (j+1-k) ∧ s (k+1)=s (j-k) := by
    intro k
    induction k with
    | zero => intro _; simpa only [Nat.sub_zero,Nat.zero_add] using And.intro r0.symm r1.symm
    | succ k ih =>
      intro h
      obtain ⟨C,D⟩ := ih (by omega)
      refine ⟨by simpa [show j+1-(k+1)=j-k by omega] using D,?_⟩
      have jp : 0<j-k := by omega
      have N1 : j-k+1=j+1-k := by omega
      have N2 : j-(k+1)+1=j-k := by omega
      have N3 : j-(k+1)+2=j+1-k := by omega
      have a1 : R (s (k+1)) (s k) := symm (edges k)
      have a2 : R (s (k+1)) (s (k+2)) := edges (k+1)
      have a3 : R (s (k+1)) (s (j-(k+1))) := by
        rw [D,←N2]
        exact symm (edges _)
      have b1 := noBounce k
      have b2 : s (j-(k+1))≠s k := by
        rw [C,←N3]
        exact (noBounce _).symm
      exact unique _ _ _ _ a1 a2 a3 b1 b2
  by_cases even : j%2=0
  · let k := j/2
    have q0 : k≤j := by omega
    have q : j+1-k=k+1 := by omega
    have eq := (mirror k q0).1
    rw [q] at eq
    have Z := edges k
    rw [←eq] at Z
    exact loop _ Z
  · let k := j/2
    have q0 : k≤j := by omega
    have q : j+1-k=k+2 := by omega
    have eq := (mirror k q0).1
    rw [q] at eq
    exact noBounce k eq.symm

end HaarDerivedReflect
#print axioms HaarDerivedReflect.reverse_forces_branch
