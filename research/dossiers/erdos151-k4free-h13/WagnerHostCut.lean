import WagnerHallMass
import WagnerMinority
import Mathlib.Data.Finset.Prod

open scoped BigOperators
namespace Erdős151.H12.Wagner
variable {V L R : Type*} [Fintype V] [Fintype L] [Fintype R]
  [DecidableEq V] [DecidableEq L] [DecidableEq R]

def hostRel (E : L ↪ Finset V) (u v : V) : Prop :=
  ∃ e : L, u ∈ E e ∧ v ∈ E e

def hostMixed (E : L ↪ Finset V) (S : Finset L) (v : V) : Prop :=
  ∃ s ∈ S, ∃ t : L, t ∉ S ∧ v ∈ E s ∧ v ∈ E t

/-- The only local-link property needed by the proof: every nontrivial
partition of the spokes exposes at least three distinct split triangles. -/
def localSplit (E : L ↪ Finset V) (T : R ↪ Finset V) : Prop :=
  ∀ S : Finset L, ∀ v : V, hostMixed E S v →
    ∃ J : Finset R, 3 ≤ J.card ∧ ∀ t ∈ J,
      ∃ e ∈ S, ∃ f : L, f ∉ S ∧ v ∈ E e ∧ v ∈ E f ∧ E e ⊆ T t ∧ E f ⊆ T t

theorem card_inc_product (A : L → R → Prop) [DecidableRel A]
    (S : Finset L) (T : Finset R) :
    ((S ×ˢ T).filter (fun a => A a.1 a.2)).card = mass A S T := by
  rw [Finset.card_filter,Finset.sum_product]
  rfl

/-- Checked bridge from host-level mixed vertices to the Hall obstruction
interface. Local links, global vertex deletion, and the square itself are
supplied separately. -/
theorem small_host_cut (E : L ↪ Finset V) (Tr : R ↪ Finset V)
    (ec : ∀ e, (E e).card = 2) (tc : ∀ t, (Tr t).card = 3)
    (hn : 4 ≤ Fintype.card V)
    (hlinks : localSplit E Tr)
    (glob : ∀ U : Finset V, U.card ≤ 3 → ∀ a b : V, a ∉ U → b ∉ U →
      Relation.ReflTransGen (fun x y => hostRel E x y ∧ x ∉ U ∧ y ∉ U) a b)
    (P : Finset L) (hp : 4 ≤ P.card)
    (S : Finset L) (T : Finset R) (dS : Disjoint S P) (hs : 3 ≤ S.card)
    (hcut : cutMass (fun e t => E e ⊆ Tr t) S T ≤ 5) :
    mass (fun e t => E e ⊆ Tr t) S T < S.card + T.card := by
  classical
  let r (e : L) (t : R) := E e ⊆ Tr t
  let A := ((S ×ˢ (Finset.univ \ T)).filter fun a => r a.1 a.2)
  let B := ((((Finset.univ : Finset L) \ S) ×ˢ T).filter fun a => r a.1 a.2)
  let C := A ∪ B
  let U := (Finset.univ : Finset V).filter (hostMixed E S)
  have dis : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    have x1 := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    have x2 := (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1).2
    exact x2 x1
  have cc : C.card = cutMass r S T := by
    rw [show C=A∪B from rfl,Finset.card_union_of_disjoint dis]
    dsimp only [A,B]
    exact congrArg₂ Nat.add (card_inc_product r S (Finset.univ \ T))
      (card_inc_product r (Finset.univ \ S) T)
  let q (v : V) := (C.filter fun a => v ∈ E a.1).card
  have hq : ∀ v ∈ U, 3 ≤ q v := by
    intro v hv
    obtain ⟨J,hJ,hp⟩ := hlinks S v (Finset.mem_filter.mp hv).2
    have chooseE (t : ↥J) : ∃ e : L,
        (e,t.val) ∈ C.filter (fun a => v ∈ E a.1) := by
      obtain ⟨e,he,f,hf,hve,hvf,het,hft⟩ := hp t.val t.property
      by_cases ht : t.val ∈ T
      · exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hf⟩,ht⟩,hft⟩)),hvf⟩⟩
      · exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨he,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ht⟩⟩,het⟩)),hve⟩⟩
    choose f hf using chooseE
    have inj : Function.Injective (fun t : ↥J =>
        (⟨(f t,t.val),hf t⟩ : ↥(C.filter fun a => v ∈ E a.1))) := by
      intro a b h
      exact Subtype.ext (congrArg (fun x => x.val.2) h)
    have hcard := Fintype.card_le_of_injective _ inj
    simpa [q] using hJ.trans (show J.card ≤ (C.filter fun a => v ∈ E a.1).card by simpa using hcard)
  have hglobal := WagnerMinority.charge_le_twice U C (fun a => E a.1)
    (fun a _ => (ec a.1).le)
  have cm : U.card ≤ 3 := by
    have ha : (∑ _v ∈ U, (3:ℕ)) ≤ ∑ v ∈ U, q v :=
      Finset.sum_le_sum fun v hv => hq v hv
    simp only [Finset.sum_const,Nat.nsmul_eq_mul] at ha
    change (∑ v ∈ U, q v) ≤ 2 * C.card at hglobal
    have : C.card ≤ 5 := cc.le.trans hcut
    omega
  have hnonfull : ∃ root : V, root ∉ U := by
    by_contra! h
    have eq : U = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [eq,Finset.card_univ] at cm
    omega
  obtain ⟨root,hr⟩ := hnonfull
  let side (v : V) := decide (∃ e ∈ S, v ∈ E e)
  have pure (v : V) (hv : v ∉ U) (e : L) (he : v ∈ E e) :
      decide (e ∈ S) = side v := by
    by_cases hx : e ∈ S
    · simp [side,hx,show ∃ a ∈ S, v ∈ E a from ⟨e,hx,he⟩]
    · have H : ¬ ∃ a ∈ S, v ∈ E a := by
        rintro ⟨a,ha,hva⟩
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,ha,e,hx,hva,he⟩⟩)
      simp [side,hx,H]
  have same (v : V) (hv : v ∉ U) : side root = side v := by
    have path := glob U cm root v hr hv
    induction path with
    | refl => rfl
    | tail _ h ih =>
      obtain ⟨⟨e,hx,hy⟩,x,y⟩ := h
      exact (ih x).trans ((pure _ x e hx).symm.trans (pure _ y e hy))
  have minor (e : L) (h : decide (e ∈ S) ≠ side root) : E e ⊆ U := by
    intro v hv
    by_contra! hn
    exact h ((pure v hn e hv).trans (same v hn).symm)
  cases hside : side root with
  | false =>
    have hS : ∀ e ∈ S.map E, e ⊆ U ∧ e.card = 2 := by
      intro e he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
      exact ⟨minor x (by simp [hx,hside]),ec x⟩
    have H := WagnerMinority.minority_incidence U (S.map E) (T.map Tr) cm hS
      (fun t ht => by obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp ht; exact tc x)
    simp only [Finset.sum_map,Finset.card_map] at H
    rw [transpose]
    have z (t : R) : (S.map E |>.filter (· ⊆ Tr t)).card =
        ∑ s ∈ S, if E s ⊆ Tr t then (1:ℕ) else 0 := by
      rw [Finset.card_filter,Finset.sum_map]
    simp_rw [z] at H
    omega
  | true =>
    have hP : ∀ e ∈ P.map E, e ⊆ U ∧ e.card = 2 := by
      intro e he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
      have hxS : x ∉ S := fun h => Finset.disjoint_left.mp dS h hx
      exact ⟨minor x (by simp [hxS,hside]),ec x⟩
    have h := WagnerMinority.edge_card_small U (P.map E) cm hP
    simp only [Finset.card_map] at h
    omega

#print axioms small_host_cut
end Erdős151.H12.Wagner
