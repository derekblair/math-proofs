import Mathlib

/-!
Fixed transit delays in Hussak and Trehan, Termination of amnesiac flooding,
Distributed Computing 36 (2023), §4.2 and Open Problems 2–5.
https://doi.org/10.1007/s00446-023-00448-y

The square refutes Open Problem 2's universal termination claim and
Theorem 4.3. Cylinder and torus refute the universal assertions in Open
Problem 5. The clearance and directional examples are negative instances
for classification Problems 3 and 4, not classifications.
Time 0 is the activation tick; all arc lists are in a fixed order.
-/

namespace FixedDelayFlooding

abbrev Arc := Nat × Nat

structure Graph where
  arcs : List Arc
  slow : List Arc
deriving DecidableEq

structure Pending where
  soon : List Arc
  later : List Arc
deriving DecidableEq, Repr

def idle : Pending := ⟨[], []⟩

def symmetric (edges : List Arc) : List Arc :=
  edges.flatMap (fun e => [e, (e.2, e.1)])

def first (g : Graph) (sources : List Nat) : Pending :=
  ⟨g.arcs.filter (fun e => sources.contains e.1 && !g.slow.contains e),
   g.arcs.filter (fun e => sources.contains e.1 && g.slow.contains e)⟩

def sends (received : List Arc) (e : Arc) : Bool :=
  received.any (fun a => a.2 == e.1) && !received.contains (e.2, e.1)

/-- Move the messages due next tick to the receiving endpoints.
An arriving message suppresses the return arc for this tick only. -/
def step (g : Graph) (p : Pending) : Pending :=
  ⟨g.arcs.filter (fun e => p.later.contains e ||
     (sends p.soon e && !g.slow.contains e)),
   g.arcs.filter (fun e => sends p.soon e && g.slow.contains e)⟩

def orbit {T : Type} (next : T → T) (start : T) : Nat → T
  | 0 => start
  | n + 1 => next (orbit next start n)

theorem fixed_future {T : Type} (next : T → T) (start stop : T)
    (hfix : next stop = stop) {n : Nat} (h : orbit next start n = stop)
    (m : Nat) : orbit next start (n+m) = stop := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    change next (orbit next start (n+m)) = stop
    rw [ih,hfix]

theorem same_future {T : Type} (next : T → T) (start : T) {u v : Nat}
    (h : orbit next start u = orbit next start v) (k : Nat) :
    orbit next start (u+k) = orbit next start (v+k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    change next (orbit next start (u+k)) = next (orbit next start (v+k))
    rw [ih]

theorem nontermination_of_cycle {T : Type} (next : T → T) (start stop : T)
    (hfix : next stop = stop) {a p : Nat} (hp : 0 < p)
    (h : orbit next start a = orbit next start (a+p))
    (hne : orbit next start a ≠ stop) : ∀ n, orbit next start n ≠ stop := by
  intro n hn
  have repeated (k : Nat) : orbit next start (a+p*k) = orbit next start a := by
    induction k with
    | zero => simp
    | succ k ih =>
      have shift := same_future next start h (p*k)
      rw [Nat.mul_succ, show a + (p*k+p) = (a+p)+p*k by omega]
      exact shift.symm.trans ih
  have reach : n ≤ a+p*n := by
    have hn' := Nat.mul_le_mul_right n (show 1 ≤ p by omega)
    simp only [Nat.one_mul] at hn'
    omega
  have tail := fixed_future next start stop hfix hn (a+p*n-n)
  rw [show n+(a+p*n-n) = a+p*n by omega, repeated n] at tail
  exact hne tail

def run (g : Graph) (sources : List Nat) : Nat → Pending :=
  orbit (step g) (first g sources)

theorem step_idle (g : Graph) : step g idle = idle := by
  simp [step, idle, sends]

theorem fixed_nontermination (g : Graph) (s : List Nat) {a p : Nat}
    (hp : 0 < p) (h : run g s a = run g s (a+p)) (hne : run g s a ≠ idle) :
    ∀ n, run g s n ≠ idle :=
  nontermination_of_cycle (step g) (first g s) idle (step_idle g) hp h hne

def squareEdges : List Arc := [(0,1),(1,2),(2,3),(3,0)]
def square : Graph := ⟨symmetric squareEdges, [(0,1),(1,0)]⟩

theorem square_nontermination : ∀ n, run square [0,1,2] n ≠ idle :=
  fixed_nontermination square [0,1,2] (a := 3) (p := 5)
    (by decide) (by decide) (by decide)

theorem square_repeated_state :
    run square [0,1,2] 3 = ⟨[(2,3),(3,2)], []⟩ ∧
    run square [0,1,2] 8 = ⟨[(2,3),(3,2)], []⟩ := by decide

theorem square_bipartite :
    square.arcs.all (fun e => e.1 % 2 != e.2 % 2) = true := by decide

def twoSources : Graph :=
  ⟨symmetric [(0,2),(0,3),(0,4),(1,2),(1,3)], symmetric [(0,2)]⟩

theorem exactly_two_sources_nontermination :
    ∀ n, run twoSources [1,4] n ≠ idle :=
  fixed_nontermination twoSources [1,4] (a := 4) (p := 5)
    (by decide) (by decide) (by decide)

def cylinderEdges : List Arc :=
  squareEdges ++ [(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]
def cylinder : Graph := ⟨symmetric cylinderEdges, symmetric [(0,1),(1,2)]⟩

theorem cylinder_nontermination : ∀ n, run cylinder [0,3] n ≠ idle :=
  fixed_nontermination cylinder [0,3] (a := 7) (p := 5)
    (by decide) (by decide) (by decide)

def torusEdges : List Arc :=
  [(0,3),(0,1),(1,4),(1,2),(2,5),(2,0),(3,6),(3,4),(4,7),
   (4,5),(5,8),(5,3),(6,0),(6,7),(7,1),(7,8),(8,2),(8,6)]
def torus : Graph := ⟨symmetric torusEdges, symmetric [(0,3),(0,1)]⟩

theorem torus_nontermination : ∀ n, run torus [0,2] n ≠ idle :=
  fixed_nontermination torus [0,2] (a := 7) (p := 5)
    (by decide) (by decide) (by decide)

def directional : Graph :=
  ⟨symmetric [(0,1),(0,2),(0,4),(1,3),(2,3),(2,4)], [(0,1)]⟩

theorem directional_nontermination : ∀ n, run directional [0] n ≠ idle :=
  fixed_nontermination directional [0] (a := 3) (p := 9)
    (by decide) (by decide) (by decide)

structure ResetState where
  pending : Pending
  activeSlow : List Arc
  unusedSlow : List Arc
deriving DecidableEq, Repr

def touches (traffic : List Arc) (e : Arc) : Bool :=
  traffic.contains e || traffic.contains (e.2, e.1)

def startReset (g : Graph) (sources : List Nat) : ResetState :=
  let p := first g sources
  ⟨p, g.slow, g.slow.filter (fun e => !touches p.later e)⟩

/-- Once a delayed edge has been used, it returns to length one at the
first tick when neither direction of that edge has a message in transit.
The clearance check precedes the outgoing transmissions at this tick. -/
def resetStep (edges : List Arc) (state : ResetState) : ResetState :=
  let slow := state.activeSlow.filter (fun e =>
    state.unusedSlow.contains e || touches state.pending.later e)
  let p := step ⟨edges, slow⟩ state.pending
  ⟨p, slow, state.unusedSlow.filter (fun e => !touches p.later e)⟩

def clearSquare : Graph :=
  ⟨symmetric squareEdges, symmetric [(0,1),(3,0)]⟩

def clearRun : Nat → ResetState :=
  orbit (resetStep clearSquare.arcs) (startReset clearSquare [1])

theorem clear_square_state :
    clearRun 4 = ⟨⟨[(0,1),(3,2)], []⟩, [], []⟩ ∧
    clearRun 8 = ⟨⟨[(0,1),(3,2)], []⟩, [], []⟩ := by decide

theorem clear_square_nontermination :
    ∀ n, (clearRun n).pending ≠ idle := by
  intro n hn
  -- A no-message state stays a no-message state regardless of unused delays.
  have hpersist (k : Nat) : (clearRun (n+k)).pending = idle := by
    induction k with
    | zero => simpa using hn
    | succ k ih =>
      rw [Nat.add_succ]
      change (resetStep clearSquare.arcs (clearRun (n+k))).pending = idle
      simp [resetStep, ih, step_idle]
  have cycleEq : clearRun 4 = clearRun (4+4) := by decide
  have repeated (k : Nat) : clearRun (4+4*k) = clearRun 4 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := same_future (resetStep clearSquare.arcs)
        (startReset clearSquare [1]) cycleEq (4*k)
      change clearRun (4+4*k) = clearRun (4+4+4*k) at h
      rw [show 4+4*(k+1) = 4+4+4*k by omega]
      exact h.symm.trans ih
  have lateIdle := hpersist (4+4*n-n)
  rw [show n+(4+4*n-n) = 4+4*n by omega, repeated n] at lateIdle
  have awake : (clearRun 4).pending ≠ idle := by decide
  exact awake lateIdle

/-- Equation (19) of the paper, restricted to the five tick coordinates
of the weighted square. Tick coordinate 1 is not a real vertex. -/
def canMeet (v w : Fin 5) : Prop :=
  ∃ r : Fin 5, v+r = w-r ∧ v+r ≠ 1

theorem collision_not_transitive :
    canMeet 0 3 ∧ canMeet 3 2 ∧ ¬ canMeet 0 2 := by
  unfold canMeet
  decide

theorem square_exact_graph : ∀ u v : Fin 4,
    (((u:Nat),(v:Nat)) ∈ square.arcs ↔ v=u+1 ∨ u=v+1) ∧
    (((u:Nat),(v:Nat)) ∈ square.slow ↔ (u=0 ∧ v=1) ∨ (u=1 ∧ v=0)) := by
  decide

theorem exact_two_sources_bipartite :
    twoSources.arcs.all (fun e => (e.1 < 2) != (e.2 < 2)) = true := by decide

def adjacent4 (a b : Fin 4) : Prop := b=a+1 ∨ a=b+1
def adjacent3 (a b : Fin 3) : Prop := b=a+1 ∨ a=b+1
def cylinderVertex (i : Fin 4) (j : Fin 2) : Nat := 4*j.val+i.val
def torusVertex (i j : Fin 3) : Nat := 3*i.val+j.val

theorem cylinder_exact_product : ∀ (i k : Fin 4) (j l : Fin 2),
    (cylinderVertex i j,cylinderVertex k l) ∈ cylinder.arcs ↔
      (j=l ∧ adjacent4 i k) ∨ (i=k ∧ j≠l) := by
  unfold adjacent4
  decide

theorem torus_exact_product : ∀ i j k l : Fin 3,
    (torusVertex i j,torusVertex k l) ∈ torus.arcs ↔
      (j=l ∧ adjacent3 i k) ∨ (i=k ∧ adjacent3 j l) := by
  unfold adjacent3
  decide

end FixedDelayFlooding
#print axioms FixedDelayFlooding.square_nontermination
#print axioms FixedDelayFlooding.exactly_two_sources_nontermination
#print axioms FixedDelayFlooding.cylinder_nontermination
#print axioms FixedDelayFlooding.torus_nontermination
#print axioms FixedDelayFlooding.clear_square_nontermination
#print axioms FixedDelayFlooding.directional_nontermination
#print axioms FixedDelayFlooding.collision_not_transitive
#print axioms FixedDelayFlooding.cylinder_exact_product
#print axioms FixedDelayFlooding.torus_exact_product
