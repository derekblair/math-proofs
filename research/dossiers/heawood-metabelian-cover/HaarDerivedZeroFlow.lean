import HaarDerivedArms
import HaarDerivedReflect

namespace HaarDerivedZeroFlow
open HaarDerivedFlowPositive HaarDerivedArms HaarDerivedReflect
open scoped Sym2
variable {V : Type*} [DecidableEq V]

def Used (a : Nat → V) (N : Nat) (u v : V) : Prop :=
  ∃ i : Fin N, a i.val=u ∧ a (i.val+1)=v

theorem period_mod (a : Nat → V) (N : Nat) (period : ∀ i, a (i+N)=a i) (i : Nat) :
    a (i%N)=a i := by
  have rep (r k : Nat) : a (r+k*N)=a r := by
    induction k with
    | zero => simp
    | succ k IH => rw [Nat.succ_mul,←Nat.add_assoc,period,IH]
  have E : i%N+i/N*N=i := by simpa only [Nat.mul_comm (i/N) N] using Nat.mod_add_div i N
  have Z := rep (i%N) (i/N)
  rwa [E,eq_comm] at Z

theorem used_step (a : Nat → V) (N : Nat) (N0 : 0<N)
    (period : ∀ i, a (i+N)=a i) (i : Nat) :
    Used a N (a i) (a (i+1)) := by
  refine ⟨⟨i%N,Nat.mod_lt _ N0⟩,period_mod a N period i,?_⟩
  have E : (i%N+1)%N=(i+1)%N := by
    rw [Nat.add_mod (i%N),Nat.mod_mod,Nat.add_mod i]
  have Z := period_mod a N period (i%N+1)
  rw [E,period_mod a N period (i+1)] at Z
  exact Z.symm

def darts (a : Nat → V) (N : Nat) : Finset (V × V) :=
  Finset.univ.image (fun i : Fin N => (a i.val,a (i.val+1)))

def usedEdges (a : Nat → V) (N : Nat) : Finset (Sym2 V) :=
  (darts a N).image (fun p => s(p.1,p.2))

theorem dart_mem (a : Nat → V) (N : Nat) (u v : V) :
    (u,v)∈darts a N ↔ Used a N u v := by
  constructor
  · intro H
    obtain ⟨i,_,e⟩ := Finset.mem_image.mp H
    exact ⟨i,congrArg Prod.fst e,congrArg Prod.snd e⟩
  · rintro ⟨i,hu,hv⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Prod.ext hu hv⟩

theorem sparse_support (a : Nat → V) (N : Nat)
    (loopless : ∀ i, a (i+1)≠a i)
    (reverse : ∀ {u v}, Used a N u v → Used a N v u) :
    2*(usedEdges a N).card≤N := by
  classical
  let D := darts a N
  let E := usedEdges a N
  have pick (e : E) : ∃ p : V × V, p∈D ∧ s(p.1,p.2)=e.val := by
    obtain ⟨p,pm,pe⟩ := Finset.mem_image.mp e.property
    exact ⟨p,pm,pe⟩
  let P (e : E) := Classical.choose (pick e)
  have M (e : E) : P e∈D := (Classical.choose_spec (pick e)).1
  have U (e : E) : s((P e).1,(P e).2)=e.val := (Classical.choose_spec (pick e)).2
  have X (e : E) : (P e).1≠(P e).2 := by
    obtain ⟨i,hi,hj⟩ := (dart_mem a N _ _).mp (M e)
    intro eq
    exact loopless i (hj.trans (eq.symm.trans hi.symm))
  have SW (e : E) : (P e).swap∈D :=
    (dart_mem a N _ _).mpr (reverse ((dart_mem a N _ _).mp (M e)))
  let mp (q : E × Bool) : D := if q.2 then ⟨(P q.1).swap,SW q.1⟩ else ⟨P q.1,M q.1⟩
  have W (q : E × Bool) : s((mp q).val.1,(mp q).val.2)=q.1.val := by
    rcases q with ⟨e,b⟩
    cases b
    · exact U e
    · exact (Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)).trans (U e)
  have inj : Function.Injective mp := by
    rintro ⟨e,b⟩ ⟨d,k⟩ H
    have eq : e.val=d.val := (W (e,b)).symm.trans ((congrArg (fun q : D => s(q.val.1,q.val.2)) H).trans (W (d,k)))
    have z : e=d := Subtype.ext eq
    subst d
    cases b <;> cases k
    · rfl
    · exact False.elim (X e (congrArg (fun a : D => a.val.1) H))
    · exact False.elim (X e (congrArg (fun a : D => a.val.1) H).symm)
    · rfl
  have C := Fintype.card_le_of_injective mp inj
  have C' : 2*E.card≤D.card := by simpa [Nat.mul_comm] using C
  exact C'.trans ((Finset.card_image_le).trans (by simp [D,darts]))

theorem zero_bound (a : Nat → V) (N h : Nat) (N0 : 0<N)
    (R : V → V → Prop) (adj : ∀ i, R (a i) (a (i+1)))
    (noLoop : ∀ v, ¬R v v) (symmetric : ∀ {u v}, R u v → R v u)
    (girth : ∀ k, 3≤k → Cyclic R k → 2*h≤k)
    (period : ∀ i, a (i+N)=a i)
    (noBounce : ∀ i, a (i+2)≠a i)
    (reverse : ∀ {u v}, Used a N u v → Used a N v u) :
    6*h≤N := by
  classical
  let U := Used a N
  have used (i : Nat) : U (a i) (a (i+1)) := used_step a N N0 period i
  have useAdj {u v : V} (H : U u v) : R u v := by
    obtain ⟨i,hu,hv⟩ := H
    simpa [hu,hv] using adj i.val
  obtain ⟨j,Hj,Hj'⟩ := reverse (used 0)
  obtain ⟨u,T,Tinj,Tadj⟩ := reverse_forces_branch U a j.val used
    (fun b Hb => noLoop b (useAdj Hb)) reverse noBounce Hj' Hj
  have extend {z w : V} (uw : U z w) : ∃ b, U w b ∧ b≠z := by
    obtain ⟨i,hz,hw⟩ := uw
    refine ⟨a (i.val+2),?_,?_⟩
    · simpa only [hw,Nat.add_assoc] using used (i.val+1)
    · simpa only [hz] using noBounce i.val
  let W := {p : V × V // U p.1 p.2}
  let more (v : W) : W :=
    ⟨(v.val.2, Classical.choose (extend v.property)),(Classical.choose_spec (extend v.property)).1⟩
  let path (t : Fin 3) : Nat → W := Nat.rec ⟨(u,T t),Tadj t⟩ (fun _ d => more d)
  let A (t : Fin 3) : Nat → V := fun i => match i with
    | 0 => u
    | k+1 => (path t k).val.2
  have e (t : Fin 3) (i : Nat) : U (A t i) (A t (i+1)) := by
    cases i with
    | zero => exact Tadj t
    | succ i => exact (path t (i+1)).property
  have b (t : Fin 3) (i : Nat) : A t (i+2)≠A t i := by
    cases i with
    | zero => exact (Classical.choose_spec (extend (path t 0).property)).2
    | succ i => exact (Classical.choose_spec (extend (path t (i+1)).property)).2
  have arms := count_arms R h girth noLoop symmetric (usedEdges a N) u A (fun _ => rfl) Tinj
    (fun t i _ => useAdj (e t i)) (fun t i _ => b t i)
    (fun t i _ => Finset.mem_image.mpr ⟨(A t i,A t (i+1)),(dart_mem a N _ _).mpr (e t i),rfl⟩)
  have twice := sparse_support a N (fun i eq => noLoop _ (by simpa [eq] using adj i)) reverse
  omega

end HaarDerivedZeroFlow
#print axioms HaarDerivedZeroFlow.zero_bound
