import KProjection

namespace KPhase
open KProjection
open PhaseProduct (Machine Node sign s phase sign_sq)
open PhaseFinite (Coord)

variable {D : Finset ℤ} {f : ℤ → List ℤ} {k : ℕ}
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (u v : ℤ × ℤ) (neg : Bool) (m : ℤ)

abbrev Q (D : Finset ℤ) (k : ℕ) := KTrace.St D k
abbrev E (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ) := KTrace.Ed D f k

structure PNode (Q : Type*) (k : ℕ) where
  loc : Q
  x : Fin k → ℤ
  bit : Bool

def bit (neg b : Bool) := b ^^ neg

def localMachine (j : Fin k) : Machine (Q D k) (E D f k) :=
  ⟨KFinite.src,KFinite.dst closed,ex v j,nu u j,m,neg⟩

def next (e : E D f k) (p : PNode (Q D k) k) : PNode (Q D k) k :=
  ⟨KFinite.dst closed e, fun j => m*p.x j + ex v j e, bit neg p.bit⟩

def cost (u : ℤ × ℤ) (neg : Bool) (e : E D f k) (q : Bool) : Fin k → ℤ :=
  fun j => sign (bit neg q) * nu u j e

def aug (p : PNode (Q D k) k) : List (E D f k) → PNode (Q D k) k
  | [] => p
  | e::es => aug (next closed v neg m e p) es

def costs (u : ℤ × ℤ) (neg : Bool) (q : Bool) : List (E D f k) → (Fin k → ℤ)
  | [] => 0
  | e::es => cost u neg e q + costs u neg (bit neg q) es

def coord (p : PNode (Q D k) k) (j : Fin k) : Node (Q D k) :=
  ⟨p.loc,p.x j,p.bit⟩

theorem aug_proj (p : PNode (Q D k) k) (L : List (E D f k)) (j : Fin k) :
    coord (aug closed v neg m p L) j =
      PhaseProduct.aug (localMachine closed u v neg m j) (coord p j) L := by
  induction L generalizing p with
  | nil => rfl
  | cons e L ih => exact ih _

theorem cost_proj (q : Bool) (L : List (E D f k)) (j : Fin k) :
    costs u neg q L j = (PhaseProduct.costs (localMachine closed u v neg m j) q L).sum := by
  induction L generalizing q with
  | nil => rfl
  | cons e L ih =>
    change cost u neg e q j + costs u neg (bit neg q) L j =
      cost u neg e q j + (PhaseProduct.costs (localMachine closed u v neg m j) (bit neg q) L).sum
    rw [ih]

include u in
theorem aug_x (p : PNode (Q D k) k) (L : List (E D f k)) (j : Fin k) :
    (aug closed v neg m p L).x j = ScalarTrace.zeval m (p.x j) (L.map (ex v j)) := by
  exact (congrArg Node.ex (aug_proj closed u v neg m p L j)).trans
    (PhaseProduct.aug_ex (localMachine closed u v neg m j) (coord p j) L)

theorem aug_loc {x y : Q D k} {L : List (E D f k)} (p : Fin k → ℤ) (q : Bool)
    (h : KTrace.Path D f k closed x y L) :
    (aug closed v neg m ⟨x,p,q⟩ L).loc = y := by
  induction h generalizing p q with
  | nil => rfl
  | cons e h ih => exact ih _ _

include closed v m in
theorem zero_iff (x : Q D k) (q : Bool) (L : List (E D f k)) :
    (∀ j : Fin k, ScalarTrace.zeval (sign neg) 0 (L.map (nu u j)) = 0) ↔
      costs u neg q L = 0 := by
  have each (j : Fin k) := PhaseProduct.zero_iff (localMachine closed u v neg m j) ⟨x,0,q⟩ L
  constructor
  · intro h
    funext j
    exact (cost_proj closed u v neg m q L j).trans ((each j).mp (h j))
  · intro h j
    apply (each j).mpr
    exact (cost_proj closed u v neg m q L j).symm.trans (congrFun h j)

variable (B : ℤ)

abbrev Vertex (D : Finset ℤ) (k : ℕ) (B : ℤ) := Q D k × (Fin k → Coord B) × Bool

def into (p : Vertex D k B) : PNode (Q D k) k :=
  ⟨p.1,fun j => (p.2.1 j).val,p.2.2⟩

def pack (p : PNode (Q D k) k) (h : ∀ j, p.x j ∈ IntegerTrace.box B) : Vertex D k B :=
  ⟨p.loc,fun j => ⟨p.x j,h j⟩,p.bit⟩

def arcCondition (t : E D f k × (Fin k → Coord B) × Bool) : Prop :=
  ∀ j : Fin k, m*(t.2.1 j).val + ex v j t.1 ∈ IntegerTrace.box B

instance (t : E D f k × (Fin k → Coord B) × Bool) :
    Decidable (arcCondition v m B t) := by unfold arcCondition; infer_instance

abbrev Arc (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ) (v : ℤ × ℤ) (m B : ℤ) :=
  {t : E D f k × (Fin k → Coord B) × Bool // arcCondition v m B t}

def src (t : Arc D f k v m B) : Vertex D k B := ⟨KFinite.src t.val.1, t.val.2⟩
def dst (t : Arc D f k v m B) : Vertex D k B :=
  ⟨KFinite.dst closed t.val.1,fun j => ⟨_,t.property j⟩,bit neg t.val.2.2⟩

def label (t : Arc D f k v m B) := cost u neg t.val.1 t.val.2.2

end KPhase

#print axioms KPhase.aug_x
#print axioms KPhase.zero_iff
