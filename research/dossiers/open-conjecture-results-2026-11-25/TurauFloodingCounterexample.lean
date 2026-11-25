import Mathlib

/-!
Counterexample to the conjecture in Section 8 of Volker Turau,
"Analysis of Amnesiac Flooding", arXiv:2002.10752v4, p. 12.
https://arxiv.org/pdf/2002.10752v4#page=12

The graph is a 20-vertex path with four extra vertices, each joined to
one of the four sources and both of that source's path neighbors.
Radius 10; four sources terminate flooding in three rounds.
-/
namespace TurauFlooding

structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v=adj v u
  loopless : ∀ v, adj v v=false

inductive Walk {n : Nat} (G : Graph n) : Fin n → Fin n → Nat → Prop
  | nil (v) : Walk G v v 0
  | cons {u v w m} : G.adj u v=true → Walk G v w m → Walk G u w (m+1)

theorem walk_append {n : Nat} {G : Graph n} {u v w : Fin n} {l m : Nat}
    (a : Walk G u v l) (b : Walk G v w m) : Walk G u w (l+m) := by
  induction a with
  | nil => simpa using b
  | @cons x y z t h _ ih =>
    rw [show t+1+m=t+m+1 by omega]
    exact Walk.cons h (ih b)

theorem walk_reverse {n : Nat} {G : Graph n} {u v : Fin n} {l : Nat}
    (a : Walk G u v l) : Walk G v u l := by
  induction a with
  | nil => exact .nil _
  | @cons u v w l e _ ih =>
    have e' : G.adj v u=true := (G.symm v u).trans e
    exact walk_append ih (Walk.cons e' (.nil _))

def Connected {n : Nat} (G : Graph n) : Prop :=
  ∀ u v, ∃ l, Walk G u v l

def Bipartite {n : Nat} (G : Graph n) : Prop :=
  ∃ col : Fin n → Bool, ∀ u v, G.adj u v=true → col u ≠ col v

def RadiusLE {n : Nat} (G : Graph n) (r : Nat) : Prop :=
  ∃ c, ∀ v, ∃ l≤r, Walk G c v l

noncomputable def radius {n : Nat} (G : Graph n) : Nat := by
  classical
  exact if h : ∃ r,RadiusLE G r then Nat.find h else 0

abbrev Message (n : Nat) := Fin n × Fin n

def allArcs {n : Nat} (G : Graph n) : List (Message n) :=
  ((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u,v)))).filter
    (fun m => G.adj m.1 m.2)

theorem arc_iff {n : Nat} (G : Graph n) (u v : Fin n) :
    (u,v) ∈ allArcs G ↔ G.adj u v=true := by
  simp [allArcs]

def initial {n : Nat} (G : Graph n) (starts : Finset (Fin n)) : List (Message n) :=
  (allArcs G).filter (fun m => decide (m.1∈starts))

def advance {n : Nat} (G : Graph n) (m : List (Message n)) : List (Message n) :=
  (allArcs G).filter (fun uv =>
    m.any (fun xy => xy.2==uv.1) && !(m.contains (uv.2,uv.1)))

theorem initial_rule {n : Nat} (G : Graph n) (starts : Finset (Fin n)) (u v : Fin n) :
    (u,v) ∈ initial G starts ↔ G.adj u v=true ∧ u∈starts := by
  simp [initial,arc_iff]

theorem advance_rule {n : Nat} (G : Graph n) (m : List (Message n)) (u v : Fin n) :
    (u,v) ∈ advance G m ↔ G.adj u v=true ∧
       (∃ w, (w,u)∈m) ∧ (v,u)∉m := by
  simp only [advance,List.mem_filter,arc_iff,Bool.and_eq_true,List.any_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
  refine and_congr_right (fun _ => and_congr_left (fun _ => ?_))
  constructor
  · rintro ⟨⟨a,b⟩,hm,he⟩
    change b=u at he
    subst b
    exact ⟨a,hm⟩
  · rintro ⟨w,hw⟩
    exact ⟨(w,u),hw,rfl⟩

/-- Index zero corresponds to the first nonempty-or-empty sending round. -/
def round {n : Nat} (G : Graph n) (starts : Finset (Fin n)) : Nat → List (Message n)
  | 0 => initial G starts
  | r+1 => advance G (round G starts r)

/-- Round r being empty means at most r rounds with a send (one-based).
Empty rounds are absorbing by the protocol. -/
def FloodLE {n : Nat} (G : Graph n) (k r : Nat) : Prop :=
  ∃ starts : Finset (Fin n), starts.card=k ∧ round G starts r=[]

noncomputable def floodNumber {n : Nat} (G : Graph n) (k : Nat) : Nat := by
  classical
  exact if h : ∃ r,FloodLE G k r then Nat.find h else 0

abbrev V := Fin 24

def edges : List (V×V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),
   (10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,18),(18,19),
   (1,20),(2,20),(3,20),(6,21),(7,21),(8,21),(11,22),(12,22),(13,22),(16,23),(17,23),(18,23)]

def gAdj (u v : V) : Bool := edges.contains (u,v) || edges.contains (v,u)

def witness : Graph 24 :=
  ⟨gAdj,by intro u v; exact Bool.or_comm ..,by decide⟩

def starts : Finset V := ([2,7,12,17] : List V).toFinset

def coord (v : V) : Nat := if v.val<20 then v.val else 2+5*(v.val-20)

def rank (v : V) : Nat :=
  (coord v-9)+(9-coord v)+(if v.val<20 then 0 else 1)

def toward (v : V) : V :=
  if h20 : v.val<20 then
    if h9 : v.val<9 then ⟨v.val+1,by omega⟩ else ⟨v.val-1,by omega⟩
  else ⟨coord v,by
    have hp := v.isLt
    simp only [coord,ite_eq_right h20]
    omega⟩

theorem toward_check : ∀ v : V, v≠9 →
    witness.adj v (toward v)=true ∧ rank (toward v)+1=rank v := by decide
theorem rank_bound : ∀ v : V, rank v≤10 := by decide
theorem coord_step : ∀ u v : V, witness.adj u v=true →
    coord u ≤ coord v+1 ∧ coord v ≤ coord u+1 := by decide

theorem center_walk (v : V) : Walk witness v 9 (rank v) := by
  by_cases h : v=9
  · subst v
    exact .nil _
  · obtain ⟨ha,hr⟩ := toward_check v h
    rw [← hr]
    exact .cons ha (center_walk (toward v))
termination_by rank v
decreasing_by omega

theorem witness_connected : Connected witness := by
  intro u v
  exact ⟨rank u+rank v,walk_append (center_walk u) (walk_reverse (center_walk v))⟩

theorem witness_nonbipartite : ¬ Bipartite witness := by
  rintro ⟨c,h⟩
  have e₁ := h 1 2 (by decide)
  have e₂ := h 2 20 (by decide)
  have e₃ := h 1 20 (by decide)
  cases h₁ : c 1 <;> cases h₂ : c 2 <;> cases h₃ : c 20 <;> simp_all

theorem coord_walk {u v : V} {l : Nat} (w : Walk witness u v l) :
    coord u ≤ coord v+l ∧ coord v ≤ coord u+l := by
  induction w with
  | nil => simp
  | cons h _ ih =>
    have hp := coord_step _ _ h
    omega

theorem witness_radius : radius witness=10 := by
  classical
  have h10 : RadiusLE witness 10 :=
    ⟨9,fun v => ⟨rank v,rank_bound v,walk_reverse (center_walk v)⟩⟩
  have hx : ∃ r,RadiusLE witness r := ⟨10,h10⟩
  rw [radius,dite_eq_left hx]
  apply Nat.le_antisymm (Nat.find_min' hx h10)
  obtain ⟨v,hv⟩ := Nat.find_spec hx
  by_cases hn : coord v≤9
  · obtain ⟨l,hl,hw⟩ := hv 19
    have hh := (coord_walk hw).2
    have he : coord (19 : V)=19 := by decide
    omega
  · obtain ⟨l,hl,hw⟩ := hv 0
    have hh := (coord_walk hw).1
    have he : coord (0 : V)=0 := by decide
    omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem witness_flood : FloodLE witness 4 3 := by
  exact ⟨starts,by decide,by decide⟩

theorem witness_floodNumber : floodNumber witness 4 ≤ 3 := by
  classical
  have hex : ∃ r, FloodLE witness 4 r := ⟨3,witness_flood⟩
  rw [floodNumber,dite_eq_left hex]
  exact Nat.find_min' hex witness_flood

def TurauConjecture : Prop :=
  ∀ n (G : Graph n), Connected G → ¬Bipartite G → ∀ k, 1≤k → k≤n →
    radius G+k-1 ≤ k*floodNumber G k

theorem turau_counterexample : ¬ TurauConjecture := by
  intro h
  have hh := h 24 witness witness_connected witness_nonbipartite 4 (by decide) (by decide)
  have hr := witness_radius
  have hF := witness_floodNumber
  omega

end TurauFlooding

#print axioms TurauFlooding.turau_counterexample
