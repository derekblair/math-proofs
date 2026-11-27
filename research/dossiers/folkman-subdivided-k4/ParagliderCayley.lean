import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Basic

namespace Paraglider
variable {V : Type*}

/-- A non-induced copy of K4 with one edge subdivided once. Vertices u,v
are the degree-three ends of the subdivided edge; z is the subdivision. -/
def Contains (I : V → V → Prop) : Prop :=
  ∃ u v x y z, u≠v ∧ x≠y ∧ z≠x ∧ z≠y ∧
    I x y ∧ I u x ∧ I u y ∧ I v x ∧ I v y ∧ I u z ∧ I v z

def TwoCommon (I : V → V → Prop) : Prop :=
  ∀ u v x y, u≠v → x≠y → I x y → I u x → I u y → I v x → I v y →
    ∀ z, I u z → I v z → z=x ∨ z=y

theorem free_iff_two_common (I : V → V → Prop) : (¬Contains I) ↔ TwoCommon I := by
  classical
  constructor
  · intro h u v x y uv xy A ux uy vx vy z uz vz
    by_contra! nh
    exact h ⟨u,v,x,y,z,uv,xy,nh.1,nh.2,A,ux,uy,vx,vy,uz,vz⟩
  · rintro h ⟨u,v,x,y,z,uv,xy,zx,zy,A,ux,uy,vx,vy,uz,vz⟩
    exact (h u v x y uv xy A ux uy vx vy z uz vz).elim zx zy

section Group
variable {G : Type*} [Group G]

def cayley (S : G → Prop) (a b : G) : Prop := S (a⁻¹*b)

def InvClosed (S : G → Prop) : Prop := ∀ g, S g → S g⁻¹
def ConjClosed (S : G → Prop) : Prop := ∀ g h, S h → S (g*h*g⁻¹)

theorem adjacent_ne (S : G → Prop) (s₁ : ¬S 1) {u v : G} (adj : cayley S u v) : u≠v := by
  rintro rfl
  exact s₁ (by simpa [cayley] using adj)

theorem cay_symm (S : G → Prop) (invs : InvClosed S) {x y : G} (h : cayley S x y) :
    cayley S y x := by
  have hr := invs _ h
  have e : (x⁻¹*y)⁻¹=y⁻¹*x := by group
  rwa [e] at hr

theorem cay_left (S : G → Prop) (t : G) {x y : G} (adj : cayley S x y) :
    cayley S (t*x) (t*y) := by
  unfold cayley at *
  have e : (t*x)⁻¹*(t*y)=x⁻¹*y := by group
  rwa [e]

theorem cay_reflect (S : G → Prop) (invs : InvClosed S) (conj : ConjClosed S)
    (a b : G) {x y : G} (h : cayley S x y) :
    cayley S (a*x⁻¹*b) (a*y⁻¹*b) := by
  have h' := conj (b⁻¹*x) ((x⁻¹*y)⁻¹) (invs _ h)
  have e : (b⁻¹*x)*(x⁻¹*y)⁻¹*(b⁻¹*x)⁻¹ =
      (a*x⁻¹*b)⁻¹*(a*y⁻¹*b) := by group
  unfold cayley
  exact e ▸ h'

theorem common_pair_product (S : G → Prop) (invs : InvClosed S) (conj : ConjClosed S)
    (free : TwoCommon (cayley S)) {s u v : G}
    (ne : u≠v) (n1 : (1:G)≠s) (edge : cayley S 1 s)
    (u1 : cayley S u 1) (us : cayley S u s) (v1 : cayley S v 1) (vs : cayley S v s) :
    u*v=1 ∨ u*v=s := by
  apply free u v 1 s ne n1 edge u1 us v1 vs (u*v)
  · have h := cay_reflect S invs conj u v v1
    simpa using h
  · have h := cay_reflect S invs conj u v u1
    simpa using h

theorem distinct_product_pair_impossible {s u v w : G}
    (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (p : u*v=1) (q : u*w=s) (r : v*w=1 ∨ v*w=s) : False := by
  rcases r with h|h
  · have vv : v=u⁻¹ := by
      calc
        v = u⁻¹*(u*v) := by group
        _ = _ := by simp [p]
    have ww : w=v⁻¹ := by
      calc
        w = v⁻¹*(v*w) := by group
        _ = _ := by simp [h]
    exact uw (by simp [vv,ww])
  · exact uv (mul_right_cancel (q.trans h.symm))

theorem no_three_at_one (S : G → Prop) (invs : InvClosed S) (conj : ConjClosed S)
    (free : TwoCommon (cayley S)) {s u v w : G} (n1 : (1:G)≠s) (edge : cayley S 1 s)
    (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (u1 : cayley S u 1) (us : cayley S u s)
    (v1 : cayley S v 1) (vs : cayley S v s)
    (w1 : cayley S w 1) (ws : cayley S w s) : False := by
  have P := common_pair_product S invs conj free uv n1 edge u1 us v1 vs
  have Q := common_pair_product S invs conj free uw n1 edge u1 us w1 ws
  rcases P with p|p <;> rcases Q with q|q
  · exact vw (mul_left_cancel (p.trans q.symm))
  · exact distinct_product_pair_impossible uv uw vw p q
      (common_pair_product S invs conj free vw n1 edge v1 vs w1 ws)
  · exact distinct_product_pair_impossible uw uv vw.symm q p
      (common_pair_product S invs conj free vw.symm n1 edge w1 ws v1 vs)
  · exact vw (mul_left_cancel (p.trans q.symm))

/-- In a Cayley graph with a conjugacy-invariant, inverse-closed
connection set, forbidding the subdivided K4 forces at most two triangles
per edge. No finiteness, connectivity, or group order hypothesis. -/
theorem no_three_common (S : G → Prop) (s₁ : ¬S 1) (invs : InvClosed S)
    (conj : ConjClosed S) (free : ¬Contains (cayley S))
    {x y u v w : G} (xy : cayley S x y) (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (ux : cayley S u x) (uy : cayley S u y)
    (vx : cayley S v x) (vy : cayley S v y)
    (wx : cayley S w x) (wy : cayley S w y) : False := by
  have edge : cayley S 1 (x⁻¹*y) := by simpa [cayley] using xy
  have tr (t a : G) (h : cayley S t a) := cay_left S x⁻¹ h
  have shift (a b : G) (h : a≠b) : x⁻¹*a≠x⁻¹*b := fun e => h (mul_left_cancel e)
  have L (t : G) (h : cayley S t x) : cayley S (x⁻¹*t) 1 := by
    simpa using tr t x h
  exact no_three_at_one S invs conj ((free_iff_two_common _).mp free) (adjacent_ne S s₁ edge) edge
    (shift u v uv) (shift u w uw) (shift v w vw)
    (L u ux) (tr u y uy) (L v vx) (tr v y vy) (L w wx) (tr w y wy)

#print axioms no_three_common
end Group
end Paraglider
