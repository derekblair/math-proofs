import HaarAllNoncommuting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Group

namespace HaarMetaVoltagePullback
open HaarCycle HaarAllNoncommuting
variable {G Q B : Type*} [Group G] [Group Q]

abbrev P := Fin 3
def port (x y : G) (j : P) : G := if j.val=0 then 1 else if j.val=1 then x else y

structure Setup (f : G→*Q) (x y : G) (B : Type*) where
  next : B → P → B
  side : B → Bool
  repr : B → G
  inj : Function.Injective (fun b => (side b, f (repr b)))
  flip : ∀ b j, b≠next b j → side (next b j)= !side b
  rev : ∀ b j, b≠next b j → next (next b j) j=b
  unique : ∀ b j k, b≠next b j → next b j=next b k → j=k
  forward : ∀ b j, b≠next b j → side b=false →
    f (repr (next b j))=f (repr b) * f (port x y j)

variable {f : G→*Q} {x y : G} (T : Setup f x y B)

def good (u v : B) : Prop := T.side u=false ∧ u≠v ∧ ∃ j, T.next u j=v

noncomputable def raw (u v : B) (h : good T u v) : G :=
  T.repr u * port x y (Classical.choose h.2.2) * (T.repr v)⁻¹

theorem raw_mem (u v : B) (h : good T u v) : raw T u v h ∈ f.ker := by
  let j := Classical.choose h.2.2
  have e : T.next u j=v := Classical.choose_spec h.2.2
  have hf := T.forward u j (by rw [e]; exact h.2.1) h.1
  rw [e] at hf
  change f (T.repr u * port x y j * (T.repr v)⁻¹)=1
  rw [map_mul,map_mul,map_inv,←hf,mul_inv_cancel]

theorem raw_step (u : B) (j : P) (ne : u≠T.next u j)
    (h : good T u (T.next u j)) :
    raw T u (T.next u j) h = T.repr u*port x y j*(T.repr (T.next u j))⁻¹ := by
  unfold raw
  have e := Classical.choose_spec h.2.2
  rw [(T.unique u j (Classical.choose h.2.2) ne e.symm).symm]

variable [hc : Fact (∀ a b : f.ker, a*b=b*a)]
local instance commKernel : CommGroup f.ker where
  __ := (inferInstance : Group f.ker)
  mul_comm := hc.out
local instance addCommKernel : AddCommGroup (Additive f.ker) := inferInstance

noncomputable def weight (u v : B) : Additive f.ker := by
  classical
  exact if h : good T u v then Additive.ofMul ⟨raw T u v h,raw_mem T u v h⟩
    else if h : good T v u then -Additive.ofMul ⟨raw T v u h,raw_mem T v u h⟩
    else 0

theorem anti (u v : B) : weight T v u = -weight T u v := by
  classical
  unfold weight
  by_cases h : good T u v
  · obtain ⟨j,e⟩ := h.2.2
    have s := T.flip u j (by rw [e]; exact h.2.1)
    rw [e,h.1] at s
    have no : ¬good T v u := fun q => by simpa [s] using q.1
    simp [h,no]
  · by_cases k : good T v u <;> simp [h,k]

def point (s : B × Additive f.ker) : Bool × G :=
  (T.side s.1,(s.2.toMul : G)*T.repr s.1)

theorem point_inj : Function.Injective (point T) := by
  rintro ⟨u,a⟩ ⟨v,b⟩ E
  have s : T.side u=T.side v := congrArg Prod.fst E
  have e : (a.toMul : G)*T.repr u=(b.toMul : G)*T.repr v := congrArg Prod.snd E
  have q := congrArg f e
  rw [map_mul,map_mul,(a.toMul).property,(b.toMul).property,one_mul,one_mul] at q
  have r := T.inj (Prod.ext s q)
  subst v
  have h : a=b := Subtype.ext (mul_right_cancel e)
  rw [h]

theorem point_forward (u : B) (a b : Additive f.ker) (j : P)
    (ne : u≠T.next u j) (h : T.side u=false)
    (e : a+weight T u (T.next u j)=b) :
    HaarCycle.haarAdj x y (point T (u,a)) (point T (T.next u j,b)) := by
  classical
  have ok : good T u (T.next u j) := ⟨h,ne,j,rfl⟩
  simp only [weight,dite_eq_left ok] at e
  have q : (a.toMul : G)*raw T u (T.next u j) ok=(b.toMul : G) :=
    congrArg (fun z : Additive f.ker => (z.toMul : G)) e
  rw [raw_step T u j ne] at q
  have d : (b.toMul : G)*T.repr (T.next u j)=((a.toMul : G)*T.repr u)*port x y j := by
    rw [←q]
    group
  have s : T.side (T.next u j)=true := by rw [T.flip u j ne,h]; decide
  simp only [point,haarAdj,h,s,true_and]
  fin_cases j
  · exact Or.inl (by simpa [port] using d)
  · exact Or.inr (Or.inl (by simpa [port] using d))
  · exact Or.inr (Or.inr (by simpa [port] using d))

theorem reverse_adj {u v : Bool × G} (h : HaarCycle.haarAdj x y v u) :
    HaarCycle.haarAdj x y u v := by
  rcases u with ⟨a,g⟩
  rcases v with ⟨b,z⟩
  cases a <;> cases b <;> simp_all [HaarCycle.haarAdj]

theorem point_edge {u v : B} (a b : Additive f.ker) (j : P)
    (ne : u≠v) (hs : T.next u j=v)
    (e : a+weight T u v=b) :
    HaarCycle.haarAdj x y (point T (u,a)) (point T (v,b)) := by
  subst v
  by_cases h : T.side u=false
  · exact point_forward T u a b j ne h e
  · have ns : T.side (T.next u j)=false := by rw [T.flip u j ne]; cases z : T.side u <;> simp_all
    have r := T.rev u j ne
    have kn : T.next u j≠T.next (T.next u j) j := by rw [r]; exact ne.symm
    have ee : b+weight T (T.next u j) (T.next (T.next u j) j)=a := by
      rw [r,anti T u (T.next u j),←e,add_assoc,add_neg_cancel,add_zero]
    have hh := point_forward T (T.next u j) b a j kn ns ee
    rw [r] at hh
    exact reverse_adj hh

def CoverCycle (W : B → B → Additive f.ker) (n : ℕ) : Prop :=
  ∃ v : Fin n → B × Additive f.ker, Function.Injective v ∧
    ∀ i, let j : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        (v i).1≠(v j).1 ∧ ∃ k, T.next (v i).1 k=(v j).1 ∧ (v i).2+W (v i).1 (v j).1=(v j).2

theorem lift_cycle {n : ℕ} (c : CoverCycle T (weight T) n) :
    HaarAllNoncommuting.HasCycle x y n := by
  obtain ⟨v,vi,ve⟩ := c
  refine ⟨point T ∘ v,(point_inj T).comp vi,?_⟩
  intro i
  obtain ⟨hn,k,he,hv⟩ := ve i
  exact point_edge T _ _ k hn he hv

end HaarMetaVoltagePullback
#print axioms HaarMetaVoltagePullback.lift_cycle
