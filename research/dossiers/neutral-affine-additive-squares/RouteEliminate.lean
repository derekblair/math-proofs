import CommRegex

namespace RouteEliminate
variable {V G : Type*} [DecidableEq V] [AddCommMonoid G]
variable (E : V→V→G→Prop)

inductive Route (S : Finset V) : V→V→G→Prop
  | zero (x : V) : Route S x x 0
  | arc {x y w} : E x y w → Route S x y w
  | join {x p y a b} : p∈S → Route S x p a → Route S p y b → Route S x y (a+b)

theorem widen {S T : Finset V} (h : S⊆T) {x y w} (r : Route E S x y w) :
    Route E T x y w := by
  induction r with
  | zero x => exact .zero x
  | arc e => exact .arc e
  | join p _ _ ih ih' => exact .join (h p) ih ih'

def Loop (S : Finset V) (p : V) := AddSubmonoid.closure {w | Route E S p p w}

def Through (S : Finset V) (p x y : V) (w : G) : Prop :=
  Route E S x y w ∨ ∃ a m b, Route E S x p a ∧ m∈Loop E S p ∧ Route E S p y b ∧ a+m+b=w

theorem route_or_through {S : Finset V} {p x y : V} {w : G}
    (r : Route E (insert p S) x y w) : Through E S p x y w := by
  have self {x : G} (r : Route E S p p x) : x ∈ Loop E S p :=
    AddSubmonoid.subset_closure r
  induction r with
  | zero x => exact Or.inl (.zero x)
  | arc e => exact Or.inl (.arc e)
  | @join x q y a b h ra rb ih ih' =>
    rcases Finset.mem_insert.mp h with rfl | qi
    · rcases ih with Q | ⟨l,m,r,hl,hm,hr,e⟩ <;> rcases ih' with Q' | ⟨l',m',r',hl',hm',hr',e'⟩
      · exact Or.inr ⟨a,0,b,Q,AddSubmonoid.zero_mem _,Q',by simp⟩
      · exact Or.inr ⟨a,l'+m',r',Q,add_mem (self hl') hm',hr',by rw [←e']; abel⟩
      · exact Or.inr ⟨l,m+r,b,hl,add_mem hm (self hr),Q',by rw [←e]; abel⟩
      · exact Or.inr ⟨l,m+r+l'+m',r',hl,
          add_mem (add_mem (add_mem hm (self hr)) (self hl')) hm',hr',by rw [←e,←e']; abel⟩
    · rcases ih with Q | ⟨l,m,r,hl,hm,hr,e⟩ <;> rcases ih' with Q' | ⟨l',m',r',hl',hm',hr',e'⟩
      · exact Or.inl (.join qi Q Q')
      · exact Or.inr ⟨a+l',m',r',.join qi Q hl',hm',hr',by rw [←e']; abel⟩
      · exact Or.inr ⟨l,m,r+b,hl,hm,.join qi hr Q',by rw [←e]; abel⟩
      · exact Or.inr ⟨l,m+(r+l')+m',r',hl,
          add_mem (add_mem hm (self (.join qi hr hl'))) hm',hr',by rw [←e,←e']; abel⟩

theorem loops_insert (S : Finset V) (p : V) {m : G} (h : m∈Loop E S p) :
    Route E (insert p S) p p m := by
  induction h using AddSubmonoid.closure_induction with
  | mem w h => exact widen E (Finset.subset_insert _ _) h
  | zero => exact .zero _
  | add x y hx hy ih ih' => exact .join (Finset.mem_insert_self _ _) ih ih'

theorem pivot (S : Finset V) (p x y : V) (w : G) :
    Route E (insert p S) x y w ↔ Through E S p x y w := by
  refine ⟨route_or_through E,?_⟩
  rintro (r|⟨a,m,b,l,h,r,rfl⟩)
  · exact widen E (Finset.subset_insert _ _) r
  · have pS := Finset.mem_insert_self p S
    have H := loops_insert E S p h
    exact .join pS (.join pS (widen E (Finset.subset_insert _ _) l) H)
      (widen E (Finset.subset_insert _ _) r)

end RouteEliminate

#print axioms RouteEliminate.pivot
