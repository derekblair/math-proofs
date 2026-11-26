import KFinite

namespace KTrace
open KCut KFactors CutLift AffineAddress

variable {D : Finset ℤ} {f : ℤ → List ℤ} {k : ℕ}
variable (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D)
variable (A : (ℤ × ℤ) →+ (ℤ × ℤ))
variable (aff : ∀ x ∈ D, σ (f x) = A (σ [x]))

include aff in
theorem gaps_local {w : List ℤ} (h : ∀ z ∈ w, z ∈ D) (T : Chain w (k+1))
    (P : Offset f T) (j : Fin k) :
    gaps (desc f T P) j = A (gaps T j) + offsets (fun i => (P i).head) j := by
  have hs (X : Cut w) : ∀ z ∈ X.head, z ∈ D := by
    intro z hz
    exact h z ((congrArg (fun l : List ℤ => z ∈ l) X.decomp).mpr (by simp [hz]))
  simp only [gaps,block,offsets,offsetBlock,desc,lift,sig_append,
    FiniteTripTrace.sig_list D f A aff _ (hs _),map_sub]
  abel

include closed in
theorem iterMem (a : ℤ) (ha : a ∈ D) (n : ℕ) : ∀ z ∈ TripTrace.iter f a n, z ∈ D :=
  FiniteTripTrace.iterMem D f closed a ha n

def vertex (a : ℤ) (ha : a ∈ D) {d : ℕ}
    (T : Chain (TripTrace.iter f a d) (k+1)) : KFinite.State D (k+1) :=
  KFinite.restrictShape D T (iterMem closed a ha d)

abbrev St (D : Finset ℤ) (k : ℕ) := KFinite.State D (k+1)
abbrev Ed (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ) := KFinite.Edge D (k+1) f

inductive Path (D : Finset ℤ) (f : ℤ → List ℤ) (k : ℕ)
    (closed : ∀ x ∈ D, ∀ y ∈ f x, y ∈ D) :
    St D k → St D k → List (Ed D f k) → Prop
  | nil (x : St D k) : Path D f k closed x x []
  | cons (e : Ed D f k) {y L} : Path D f k closed (KFinite.dst closed e) y L →
      Path D f k closed (KFinite.src e) y (e::L)

theorem snoc {x y : St D k} {L : List (Ed D f k)} (h : Path D f k closed x y L)
    (e : Ed D f k) (hy : KFinite.src e = y) :
    Path D f k closed x (KFinite.dst closed e) (L++[e]) := by
  induction h with
  | nil x => rw [← hy]; exact .cons e (.nil _)
  | cons e h ih => exact .cons e (ih hy)

def run (p : Fin k → ℤ×ℤ) (L : List (Ed D f k)) (j : Fin k) : ℤ×ℤ :=
  NeutralTrace.run A (p j) (L.map (fun e => KFinite.stamp e j))

include aff in
theorem realizes (a : ℤ) (ha : a ∈ D) {d : ℕ} (T : Chain (TripTrace.iter f a d) (k+1))
    (ho : ordered T) {x y : St D k} {L : List (Ed D f k)} (h : Path D f k closed x y L)
    (hx : x = vertex closed a ha T) :
    ∃ (r : ℕ) (U : Chain (TripTrace.iter f a r) (k+1)), ordered U ∧
      y = vertex closed a ha U ∧ gaps U = run A (gaps T) L := by
  induction h generalizing d with
  | nil => exact ⟨d,T,ho,hx,rfl⟩
  | @cons e y L h ih =>
    obtain ⟨P, hp, hv, hs⟩ := KFinite.step_matches closed T (iterMem closed a ha d) ho e hx
    obtain ⟨r,U,hu,huv,hd⟩ := ih (d:=d+1) (desc f T P) hp hv
    refine ⟨r,U,hu,huv,?_⟩
    rw [hd]
    funext j
    simp only [run,List.map_cons,NeutralTrace.run]
    congr 1
    exact (gaps_local A aff (iterMem closed a ha d) T P j).trans
      (by rw [congrFun hs j]; rfl)

include aff in
theorem fromChain (a : ℤ) (ha : a ∈ D) {d : ℕ} (T : Chain (TripTrace.iter f a d) (k+1))
    (ho : ordered T) :
    ∃ L, Path D f k closed (vertex closed a ha (d:=0) (root a))
      (vertex closed a ha T) L ∧ gaps T = run A 0 L := by
  induction d with
  | zero =>
    have eq : T = root a := funext (fun i => cut_eq_root a (T i))
    subst T
    exact ⟨[],.nil _,rfl⟩
  | succ d ih =>
    obtain ⟨U,P,e⟩ := unlift_all f T
    subst T
    have hU := parent_ordered f U P ho
    obtain ⟨L,hL,rL⟩ := ih U hU
    obtain ⟨e,he,hd,hs⟩ := KFinite.step_exists closed U (iterMem closed a ha d) hU P ho
    have hd' : KFinite.dst closed e = vertex closed a ha (d:=d+1) (desc f U P) := hd
    refine ⟨L++[e],hd' ▸ snoc closed hL e he,?_⟩
    funext j
    change @gaps ((TripTrace.iter f a d).flatMap f) k (desc f U P) j = _
    rw [gaps_local A aff (iterMem closed a ha d), ← hs]
    have rj := congrFun rL j
    rw [rj]
    simp only [run,List.map_append,List.map_cons,List.map_nil,FiniteTripTrace.run_append,
      NeutralTrace.run]
    rfl

theorem strict_vertex {a : ℤ} {ha : a ∈ D} {d : ℕ} (T : Chain (TripTrace.iter f a d) (k+1)) :
    strict T ↔ (vertex closed a ha T).2 = fun _ => true := by
  constructor
  · intro h; funext j; exact decide_eq_true (h j)
  · intro h j; exact of_decide_eq_true (congrFun h j)

include aff in
theorem path_iff_actual (a : ℤ) (ha : a ∈ D) :
    (∃ y : St D k, ∃ L, Path D f k closed (vertex closed a ha (d:=0) (root a))
        y L ∧ y.2 = (fun _ => true) ∧ run A 0 L = 0) ↔
      ∃ d, Actual (TripTrace.iter f a d) k := by
  constructor
  · rintro ⟨y,L,path,final,zero⟩
    have hroot : ordered (root a : Chain [a] (k+1)) := fun _ => le_rfl
    obtain ⟨r,U,_,hy,hr⟩ := realizes closed A aff a ha (d:=0) (root a) hroot path rfl
    have eq : @gaps (TripTrace.iter f a 0) k (root a) = 0 := rfl
    rw [eq,zero] at hr
    have hyv : (vertex closed a ha U).2 = fun _ => true := (congrArg Prod.snd hy).symm.trans final
    have fin : strict U := (strict_vertex closed U).mpr hyv
    exact ⟨r,chain_to_actual U fin (fun j => congrFun hr j)⟩
  · rintro ⟨d,h⟩
    obtain ⟨T,hT,hz⟩ := of_actual h
    obtain ⟨L,hL,e⟩ := fromChain closed A aff a ha T (fun j => (hT j).le)
    have zr : gaps T = 0 := funext hz
    exact ⟨vertex closed a ha T,L,hL,(strict_vertex closed T).mp hT,e.symm.trans zr⟩

end KTrace

#print axioms KTrace.path_iff_actual
