import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

namespace HaarDerivedFlowPositive

def Cyclic {V : Type*} (R : V → V → Prop) (k : Nat) : Prop :=
  ∃ v : Fin k → V, Function.Injective v ∧
    ∀ i : Fin k, R (v i) (v ⟨(i.val+1)%k,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem trace_cycle {V : Type*} [Finite V] (R : V → V → Prop)
    (s : Nat → V) (walk : ∀ i, R (s i) (s (i+1)))
    (no_loop : ∀ a, ¬R a a) (no_two : ∀ a b, R a b → ¬R b a) :
    ∃ k, 3≤k ∧ Cyclic R k := by
  let P (k : Nat) := 0<k ∧ ∃ i, s (i+k)=s i
  have ex : ∃ k, P k := by
    obtain ⟨a,b,n,e⟩ := Finite.exists_ne_map_eq_of_infinite s
    rcases lt_or_gt_of_ne n with h|h
    · exact ⟨b-a,by omega,a,by rw [show a+(b-a)=b by omega]; exact e.symm⟩
    · exact ⟨a-b,by omega,b,by rw [show b+(a-b)=a by omega]; exact e⟩
  classical
  let k := Nat.find ex
  obtain ⟨pk,i,eq⟩ := Nat.find_spec ex
  change s (i+k)=s i at eq
  change 0<k at pk
  have min (a b : Nat) (ab : a<b) (d : s a=s b) : k≤b-a :=
    Nat.find_min' ex ⟨by omega,a,by rw [show a+(b-a)=b by omega]; exact d.symm⟩
  have ge3 : 3≤k := by
    by_contra C
    have sc : k=1 ∨ k=2 := by omega
    rcases sc with e|e
    · rw [e] at eq
      exact no_loop (s i) (by simpa only [eq] using walk i)
    · rw [e] at eq
      have r := walk (i+1)
      rw [show i+1+1=i+2 by omega,eq] at r
      exact no_two _ _ (walk i) r
  refine ⟨k,ge3,fun j => s (i+j.val),?_,?_⟩
  · intro a b d
    apply Fin.ext
    rcases lt_trichotomy a.val b.val with h|h|h
    · have m := min (i+a.val) (i+b.val) (by omega) d
      omega
    · exact h
    · have m := min (i+b.val) (i+a.val) (by omega) d.symm
      omega
  · intro a
    by_cases h : a.val+1<k
    · simpa [Nat.mod_eq_of_lt h,Nat.add_assoc] using walk (i+a.val)
    · have e : a.val+1=k := by omega
      have hh : i+a.val+1=i+k := by omega
      simpa only [e,Nat.mod_self,Nat.add_zero,hh,eq] using walk (i+a.val)

variable {V : Type*} [Fintype V]
def cost (F : V → V → ℤ) : ℤ := ∑ e : V × V, max (F e.1 e.2) 0

theorem nonzero_bound (F : V → V → ℤ) (m N g : Nat)
    (m0 : 0<m)
    (anti : ∀ u v, F v u = - F u v)
    (bal : ∀ u, (∑ v, F u v)=0)
    (div : ∀ u v, (m:ℤ) ∣ F u v)
    (ne : ∃ u v, F u v≠0)
    (bound : cost F≤(N:ℤ))
    (girth : ∀ k, 3≤k → Cyclic (fun u v => 0<F u v) k → g≤k) :
    m*g≤N := by
  have out (u : V) (prev : ∃ v, 0 < F v u) : ∃ w, 0 < F u w := by
    classical
    by_contra h
    simp only [not_exists,not_lt] at h
    obtain ⟨v,p⟩ := prev
    have negative : F u v < 0 := by rw [anti v u]; omega
    have Z : (∑ w, F u w) < 0 := by
      apply Finset.sum_neg' (fun w _ => h w)
      exact ⟨v,Finset.mem_univ _,negative⟩
    have hh : (0:ℤ)<0 := by simpa only [bal u] using Z
    exact (lt_irrefl 0) hh
  obtain ⟨u,v,neuv⟩ := ne
  have existsIncoming : Nonempty {w : V // ∃ v, 0 < F v w} := by
    by_cases b : 0<F u v
    · exact ⟨⟨v,u,b⟩⟩
    · refine ⟨⟨u,v,?_⟩⟩
      rw [anti u v]
      omega
  classical
  let W := {w : V // ∃ v, 0 < F v w}
  let succ (u : W) : W := ⟨Classical.choose (out u.val u.property),
    u.val,Classical.choose_spec (out u.val u.property)⟩
  let seq : Nat → W := Nat.rec (Classical.choice existsIncoming) (fun _ u => succ u)
  let vseq (i : Nat) : V := (seq i).val
  have edge (i : Nat) : 0<F (vseq i) (vseq (i+1)) :=
    Classical.choose_spec (out (seq i).val (seq i).property)
  have irrefl (u : V) : ¬0<F u u := by
    have h := anti u u
    omega
  have notBoth (u v : V) (h : 0<F u v) : ¬0<F v u := by rw [anti u v]; omega
  obtain ⟨k,k3,C⟩ := trace_cycle (fun u v => 0<F u v) vseq edge irrefl notBoth
  have gk := girth k k3 C
  obtain ⟨path,inj,adj⟩ := C
  let e (i : Fin k) : V × V := (path i,path ⟨(i.val+1)%k,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)
  have ei : Function.Injective e := fun _ _ eq => inj (congrArg Prod.fst eq)
  let T : Finset (V × V) := Finset.univ.map ⟨e,ei⟩
  have card : T.card=k := by simp [T]
  have lower (a : V × V) (atT : a∈T) : (m:ℤ)≤max (F a.1 a.2) 0 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp atT
    have h := adj i
    have d := div (e i).1 (e i).2
    obtain ⟨j,ex⟩ := d
    have J : (0:ℤ)<j := by
      change 0<F (e i).1 (e i).2 at h
      rw [ex] at h
      exact pos_of_mul_pos_right h (by exact_mod_cast (Nat.zero_le m))
    have E := mul_le_mul_of_nonneg_left (show (1:ℤ)≤j by omega) (show (0:ℤ)≤m by exact_mod_cast Nat.zero_le _)
    rw [mul_one,←ex] at E
    exact E.trans (le_max_left _ _)
  have K : ((k*m:Nat):ℤ)≤cost F := calc
    _ = ∑ _ ∈ T, (m:ℤ) := by simp [card]
    _ ≤ ∑ a ∈ T, max (F a.1 a.2) 0 := Finset.sum_le_sum lower
    _ ≤ cost F := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => le_max_right _ _)
  exact (Nat.mul_le_mul_left m gk).trans (by
    rw [Nat.mul_comm]
    exact_mod_cast K.trans bound)

end HaarDerivedFlowPositive
#print axioms HaarDerivedFlowPositive.nonzero_bound
