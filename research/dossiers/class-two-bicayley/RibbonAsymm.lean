import RibbonAbelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic

namespace RibbonAsymm

@[ext]
structure H where
  x : ZMod 3
  y : ZMod 3
  z : ZMod 3
  t : ZMod 5
  deriving DecidableEq

def prod (a b : H) : H := ⟨a.x+b.x,a.y+b.y,a.z+b.z+a.x*b.y,a.t+b.t⟩
def one : H := ⟨0,0,0,0⟩
def inverse (a : H) : H := ⟨-a.x,-a.y,-a.z+a.x*a.y,-a.t⟩
instance : Group H where
  mul := prod
  one := one
  inv := inverse
  mul_assoc a b c := by change prod (prod a b) c = prod a (prod b c); ext <;> simp [prod] <;> ring
  one_mul a := by change prod one a=a; ext <;> simp [prod,one]
  mul_one a := by change prod a one=a; ext <;> simp [prod,one]
  inv_mul_cancel a := by change prod (inverse a) a=one; ext <;> simp [prod,inverse,one]

def a : H := ⟨1,0,0,0⟩
def b : H := ⟨0,1,0,1⟩
def c : H := ⟨0,0,1,0⟩
theorem ca : Commute c a := by change c*a=a*c; decide +kernel
theorem cb : Commute c b := by change c*b=b*c; decide +kernel
theorem rel : a*b=b*a*c := by decide +kernel
theorem cycle16 : Ribbon.Cycle a b 16 :=
  Ribbon.cycle16 a b c ca cb rel (by decide +kernel) (by decide +kernel)

abbrev V := Bool × H
abbrev P := Fin 3
def step (s : V) (j : P) : V :=
  if j=2 then (!s.1,s.2) else
    (s.1,s.2*(if s.1 then (if j=0 then b else b⁻¹) else (if j=0 then a else a⁻¹)))

theorem adj_port {u v : V} (e : Ribbon.Adj a b u v) : ∃ j, step u j=v := by
  rcases e with ⟨hu,hv,(h|h)⟩ | ⟨hu,hv,(h|h)⟩ | ⟨s,g⟩
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [step,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [step,hu,mul_assoc] using congrArg (·*a⁻¹) h.symm
  · exact ⟨0,Prod.ext (hu.trans hv.symm) (by simpa [step,hu] using h)⟩
  · refine ⟨1,Prod.ext (hu.trans hv.symm) ?_⟩
    simpa [step,hu,mul_assoc] using congrArg (·*b⁻¹) h.symm
  · have E : (!u.1)=v.1 := by cases hu : u.1 <;> cases hv : v.1 <;> simp_all
    exact ⟨2,Prod.ext E g⟩

def left (g : H) (v : V) : V := (v.1,g*v.2)
theorem left_inj (g : H) : Function.Injective (left g) := by
  intro u v e
  have h := congrArg Prod.fst e
  have h' := congrArg Prod.snd e
  exact Prod.ext h (mul_left_cancel h')
theorem left_step (g : H) (v : V) (j : P) : left g (step v j)=step (left g v) j := by
  unfold step left
  split <;> simp [mul_assoc]

def trace {n : Nat} (hn : 0<n) (u : V) (f : Fin n → P) : Nat → V
  | 0 => u
  | i+1 => step (trace hn u f i) (f ⟨i%n,Nat.mod_lt _ hn⟩)

def good {n : Nat} (hn : 0<n) (s : Bool) (f : Fin n → P) : Prop :=
  trace hn (s,1) f n=(s,1) ∧ Function.Injective (fun i : Fin n => trace hn (s,1) f i.val)
instance {n : Nat} (hn : 0<n) (s : Bool) (f : Fin n → P) : Decidable (good hn s f) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i j, _ → i=j))

theorem cycle_good {n : Nat} (hn : 0<n) (C : Ribbon.Cycle a b n) :
    ∃ s f, good hn s f := by
  obtain ⟨v,vi,ve⟩ := C
  have parts (i : Fin n) := adj_port (ve i)
  choose f hf using parts
  let root := v ⟨0,hn⟩
  let g := root.2⁻¹
  have e (i : Nat) :
      trace hn (root.1,1) f i = left g (v ⟨i%n,Nat.mod_lt _ hn⟩) := by
    induction i with
    | zero => simp [trace,left,root,g]
    | succ i ih =>
      rw [trace,ih,←left_step,hf]
      apply congrArg (left g ∘ v)
      apply Fin.ext
      exact Nat.mod_add_mod _ _ _
  refine ⟨root.1,f,?_,?_⟩
  · simp [e,left,root,g]
  · intro i j eq
    apply vi
    apply left_inj g
    simpa [e,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using eq


def TriangleAt (u : V) : Prop :=
  ∃ v w, u≠v ∧ v≠w ∧ w≠u ∧ Ribbon.Adj a b u v ∧ Ribbon.Adj a b v w ∧ Ribbon.Adj a b w u

theorem triangle_left : TriangleAt (false,1) := by
  refine ⟨(false,a),(false,a*a),?_⟩
  unfold Ribbon.Adj
  decide +kernel

private def triangleTest (p q r : P) : Prop :=
  let u : V := (true,1)
  let v := step u p
  let w := step v q
  u≠v ∧ v≠w ∧ w≠u ∧ step w r = u
private instance (p q r : P) : Decidable (triangleTest p q r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
private theorem triangleFail : ∀ p q r : P, ¬ triangleTest p q r := by decide +kernel

theorem no_triangle_right : ¬ TriangleAt (true,1) := by
  rintro ⟨v,w,uv,vw,wu,E,F,H⟩
  obtain ⟨p,hp⟩ := adj_port E
  obtain ⟨q,hq⟩ := adj_port F
  obtain ⟨r,hr⟩ := adj_port H
  subst v
  subst w
  exact triangleFail p q r ⟨uv,vw,wu,hr⟩

/-- No automorphism can move a vertex on a triangle to one on no triangle. -/
theorem not_vertex_transitive :
    ¬ ∀ u v : V, ∃ e : V ≃ V, e u = v ∧
      ∀ x y, Ribbon.Adj a b x y ↔ Ribbon.Adj a b (e x) (e y) := by
  intro h
  obtain ⟨e,eq,adj⟩ := h (false,1) (true,1)
  obtain ⟨v,w,uv,vw,wu,E,F,H⟩ := triangle_left
  apply no_triangle_right
  rw [←eq]
  exact ⟨e v,e w,fun h => uv (e.injective h),fun h => vw (e.injective h),
    fun h => wu (e.injective h),(adj _ _).mp E,(adj _ _).mp F,(adj _ _).mp H⟩

theorem port_adj (u : V) (p : P) : Ribbon.Adj a b u (step u p) := by
  obtain ⟨side,g⟩ := u
  cases side <;> fin_cases p <;> norm_num [Ribbon.Adj,step,mul_assoc]

private theorem edge_symm {u v : V} (h : Ribbon.Adj a b u v) : Ribbon.Adj a b v u := by
  rcases h with ⟨hu,hv,h⟩|⟨hu,hv,h⟩|⟨h,k⟩
  · exact Or.inl ⟨hv,hu,h.symm⟩
  · exact Or.inr (Or.inl ⟨hv,hu,h.symm⟩)
  · exact Or.inr (Or.inr ⟨Ne.symm h,k.symm⟩)

private abbrev Reach := Relation.ReflTransGen (Ribbon.Adj a b)
private def follow : V → List P → V
  | u, [] => u
  | u, p::ps => follow (step u p) ps

private def route (side : Bool) (x y z : ZMod 3) (t : ZMod 5) : List P :=
  List.replicate x.val 0 ++ [2] ++ List.replicate ((10*y.val+6*t.val)%15) 0 ++ [2] ++
    (List.replicate (z-x*y).val [1,2,1,2,0,2,0,2]).flatten ++ (if side then [2] else [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem route_correct : ∀ (side : Bool) (x y z : ZMod 3) (t : ZMod 5),
    follow (false,1) (route side x y z t) = (side,⟨x,y,z,t⟩) := by decide +kernel

private theorem follow_reachable (u : V) (w : List P) : Reach u (follow u w) := by
  induction w generalizing u with
  | nil => exact .refl
  | cons p ps ih => exact (ih (step u p)).head (port_adj u p)

private theorem from_root (u : V) : Reach (false,1) u := by
  obtain ⟨side,⟨x,y,z,t⟩⟩ := u
  simpa only [route_correct] using follow_reachable (false,1) (route side x y z t)

theorem connected (u v : V) : Reach u v := by
  have H (z : V) : Reach z (false,1) := by
    have P := from_root z
    induction P with
    | refl => exact .refl
    | tail _ e ih => exact ih.head (edge_symm e)
  exact (H u).trans (from_root v)

def coord : H ≃ ZMod 3 × ZMod 3 × ZMod 3 × ZMod 5 where
  toFun g := (g.x,g.y,g.z,g.t)
  invFun g := ⟨g.1,g.2.1,g.2.2.1,g.2.2.2⟩
  left_inv := by intro u; cases u; rfl
  right_inv := by rintro ⟨w,x,y,z⟩; rfl

theorem vertices : Nat.card V = 270 := by
  rw [Nat.card_prod, Nat.card_congr coord]
  repeat rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, ZMod.card]

set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem none4 : ∀ (s : Bool) (f : Fin 4 → P), ¬good (by decide) s f := by decide +kernel
private theorem split8 (s : Bool) (x y : P) :
    ∀ f : Fin 6 → P, ¬good (by decide) s (Fin.cons x (Fin.cons y f)) := by
  cases s <;> fin_cases x <;> fin_cases y <;> decide +kernel

theorem none8 (s : Bool) (f : Fin 8 → P) : ¬good (by decide) s f := by
  have h := split8 s (f 0) (Fin.tail f 0) (Fin.tail (Fin.tail f))
  rw [Fin.cons_self_tail,Fin.cons_self_tail] at h
  exact h

theorem sharp : ¬Ribbon.Cycle a b 4 ∧ ¬Ribbon.Cycle a b 8 ∧ Ribbon.Cycle a b 16 := by
  exact ⟨fun H => let ⟨s,f,g⟩ := cycle_good (by decide) H; none4 s f g,
    fun H => let ⟨s,f,g⟩ := cycle_good (by decide) H; none8 s f g, cycle16⟩

end RibbonAsymm
#print axioms RibbonAsymm.sharp
#print axioms RibbonAsymm.not_vertex_transitive
#print axioms RibbonAsymm.connected
#print axioms RibbonAsymm.vertices
