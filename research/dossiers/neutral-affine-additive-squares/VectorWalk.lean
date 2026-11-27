import RouteEliminate

namespace VectorWalk
open RouteEliminate CommRegex
variable {V I G : Type*} [DecidableEq V] [AddCommMonoid G]
variable (src dst : I→V) (label : I→G)

def edge (x y : V) (w : G) : Prop := ∃ i : I, src i=x ∧ dst i=y ∧ label i=w

inductive Walk : V→V→G→Prop
  | nil (x : V) : Walk x x 0
  | cons (e : I) {y w} : Walk (dst e) y w → Walk (src e) y (label e+w)

theorem append {a b c : V} {u v : G} (h : Walk src dst label a b u)
    (k : Walk src dst label b c v) : Walk src dst label a c (u+v) := by
  induction h with
  | nil => simpa using k
  | cons i p ih => simpa [add_assoc] using Walk.cons i (ih k)

theorem real_walk {S : Finset V} {a b : V} {w : G} (h : Route (edge src dst label) S a b w) :
    Walk src dst label a b w := by
  induction h with
  | zero => exact .nil _
  | arc h =>
    obtain ⟨i,rfl,rfl,rfl⟩ := h
    simpa using Walk.cons (src:=src) (dst:=dst) (label:=label) i (.nil _)
  | join _ _ _ i j => exact append src dst label i j

variable [Fintype V]
theorem walk_route {x y : V} {w : G} (h : Walk src dst label x y w) :
    Route (edge src dst label) Finset.univ x y w := by
  induction h with
  | nil => exact .zero _
  | cons e q ih =>
    exact .join (Finset.mem_univ (dst e)) (.arc ⟨e,rfl,rfl,rfl⟩) ih

def atoms : List G→Expr G
  | [] => .empty
  | x::xs => .alt (.atom x) (atoms xs)

theorem mem_atoms (L : List G) (g : G) : g ∈ image (atoms L) ↔ g∈L := by
  induction L with
  | nil => simp [atoms,image]
  | cons x L ih => simp [atoms,image,ih]

variable (pool : List I) (coverI : ∀ i : I, i∈pool)

def seeds (x y : V) : List G :=
  (pool.filter
    (fun a => decide (src a=x ∧ dst a=y))).map label

def base (x y : V) : Expr G :=
  .alt (if x=y then .atom 0 else .empty) (atoms (seeds src dst label pool x y))

include coverI in
theorem base_correct (x y : V) (g : G) :
    g∈image (base src dst label pool x y) ↔ Route (edge src dst label) ∅ x y g := by
  change (g∈image (if x=y then .atom 0 else .empty) ∨
    g∈image (atoms (seeds src dst label pool x y))) ↔ _
  rw [mem_atoms]
  have hv : g∈seeds src dst label pool x y ↔ edge src dst label x y g := by
    simp [seeds,edge,coverI]
    aesop
  rw [hv]
  constructor
  · rintro (left|e)
    · split at left
      · rename_i h
        subst y
        have r : g=0 := left
        subst g
        exact .zero _
      · exact False.elim left
    · exact .arc e
  · intro h
    cases h with
    | zero => left; simp [image]
    | arc e => exact Or.inr e
    | join q _ _ => simp at q

def compile : List V → V → V → Expr G
  | [],x,y => base src dst label pool x y
  | p::L,x,y =>
    .alt (compile L x y) (.prod (.prod (compile L x p) (.many (compile L p p))) (compile L p y))

include coverI in
theorem compile_correct (L : List V) (x y : V) (g : G) :
    g∈image (compile src dst label pool L x y) ↔ Route (edge src dst label) L.toFinset x y g := by
  induction L generalizing x y g with
  | nil => simpa [compile] using base_correct src dst label pool coverI x y g
  | cons p L ih =>
    rw [List.toFinset_cons,RouteEliminate.pivot]
    simp only [compile,image,Set.mem_union,Set.mem_setOf_eq,ih,Through]
    have e : image (compile src dst label pool L p p) =
        {w | Route (edge src dst label) L.toFinset p p w} := by ext z; exact ih p p z
    rw [e]
    simp only [Loop]
    constructor
    · rintro (h|⟨a,⟨u,hu,v,hv,rfl⟩,b,hb,rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨u,v,b,hu,hv,hb,rfl⟩
    · rintro (h|⟨a,m,b,ha,hm,hb,rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a+m,⟨a,ha,m,hm,rfl⟩,b,hb,rfl⟩

variable {J : Type*} [Fintype J] [DecidableEq J]

def decideWalk (src dst : I→V) (wt : I→J→ℤ) (pool : List I) (vertices : List V)
    (x y : V) (w : J→ℤ) : Bool :=
  CommRegex.test (compile src dst wt pool vertices x y) w

theorem decideWalk_correct (src dst : I→V) (wt : I→J→ℤ) (pool : List I) (vertices : List V)
    (coverI : ∀ i, i∈pool) (coverV : ∀ v, v∈vertices) (x y : V) (w : J→ℤ) :
    decideWalk src dst wt pool vertices x y w = true ↔ Walk src dst wt x y w := by
  have h : vertices.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using coverV)
  rw [decideWalk,CommRegex.test_iff,compile_correct src dst wt pool coverI,h]
  exact ⟨real_walk src dst wt,walk_route src dst wt⟩

end VectorWalk
#print axioms VectorWalk.decideWalk_correct
